"""Haunt Chat Wave 1 — Web Push delivery (Dan, Oct 27, 2026).

Opt-in push notifications for Haunt Chat (benchmark brief §4,
headline #1): the room can call a member back when they're
@mentioned, challenged to a word game, replied to, or when Frank
announces something new on the site. Everything here is
best-effort by design: a push failure must NEVER block or fail the
chat action that triggered it, so every public entry point swallows
its own errors and sends happen on a small daemon thread pool —
the same fire-and-forget posture as the page-view writer. The app
stays single-worker; no external queue.

VAPID keys come from the environment ONLY (never committed):
  VAPID_PRIVATE_KEY — the signing key: a PEM block (literal "\\n"
                      escapes are fine) or a base64url raw P-256
                      scalar / DER. Required.
  VAPID_PUBLIC_KEY  — optional override; derived from the private
                      key when absent. This is the
                      applicationServerKey the browser subscribes
                      with.
  VAPID_SUBJECT     — optional; defaults to the site contact
                      mailto. Push services require a contact.
If VAPID_PRIVATE_KEY is unset or unparseable, push is simply OFF:
configured() returns False, the settings UI says so, and every
send no-ops.
"""
import base64
import hashlib
import json
import logging
import os
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

from .db import get_conn

log = logging.getLogger("hauntmap.push")

KINDS = ("mentions", "challenges", "frank", "replies")
_DEFAULTS = {"enabled": 0, "mentions": 1, "challenges": 1,
             "frank": 1, "replies": 1}

# Quiet dedupe: the same (member, kind, ref) trigger inside the
# window sends once. Chat bursts already collapse mentions per
# message; this covers challenge spam and repeat replies.
_DEDUPE_WINDOW_S = 120
_recent: dict = {}
_recent_lock = threading.Lock()

_POOL = ThreadPoolExecutor(max_workers=2,
                           thread_name_prefix="webpush")


# ------------------------------------------------------------ VAPID

def _b64url_decode(text: str) -> bytes:
    text = text.strip()
    return base64.urlsafe_b64decode(text + "=" * (-len(text) % 4))


def _load_private_key():
    """Parse VAPID_PRIVATE_KEY (PEM / raw scalar / DER) -> EC key."""
    raw = (os.environ.get("VAPID_PRIVATE_KEY") or "").strip()
    if not raw:
        return None
    try:
        from cryptography.hazmat.primitives import serialization
        from cryptography.hazmat.primitives.asymmetric import ec
        if "BEGIN" in raw:
            pem = raw.replace("\\n", "\n").encode()
            return serialization.load_pem_private_key(pem, password=None)
        blob = _b64url_decode(raw)
        if len(blob) == 32:
            return ec.derive_private_key(
                int.from_bytes(blob, "big"), ec.SECP256R1())
        return serialization.load_der_private_key(blob, password=None)
    except Exception:
        log.warning("VAPID_PRIVATE_KEY is set but unparseable; "
                    "web push disabled")
        return None


def _vapid():
    """(Vapid signer, public applicationServerKey) or (None, None)."""
    key = _load_private_key()
    if key is None:
        return None, None
    try:
        from cryptography.hazmat.primitives import serialization
        from py_vapid import Vapid
        signer = Vapid()
        signer.private_key = key  # .public_key derives from this
        pub = key.public_key().public_bytes(
            serialization.Encoding.X962,
            serialization.PublicFormat.UncompressedPoint)
        pub_b64 = base64.urlsafe_b64encode(pub).rstrip(b"=").decode()
        return signer, (os.environ.get("VAPID_PUBLIC_KEY") or pub_b64)
    except Exception:
        log.warning("could not build the VAPID signer; web push "
                    "disabled", exc_info=True)
        return None, None


def configured() -> bool:
    return _load_private_key() is not None


def public_key() -> str | None:
    _, pub = _vapid()
    return pub


def _subject() -> str:
    return (os.environ.get("VAPID_SUBJECT")
            or "mailto:gethauntmap@gmail.com")


# ------------------------------------------------------------ settings

def get_settings(conn, user_id: int) -> dict:
    row = conn.execute(
        "SELECT enabled, mentions, challenges, frank, replies "
        "FROM push_settings WHERE user_id = ?", (user_id,)).fetchone()
    if row is None:
        return dict(_DEFAULTS)
    return {k: int(row[k]) for k in _DEFAULTS}


def save_settings(conn, user_id: int, values: dict) -> dict:
    cur = {k: (1 if values.get(k) else 0) for k in _DEFAULTS}
    conn.execute(
        "INSERT INTO push_settings (user_id, enabled, mentions, "
        "challenges, frank, replies, updated_at) VALUES (?, ?, ?, "
        "?, ?, ?, ?) ON CONFLICT(user_id) DO UPDATE SET enabled = "
        "excluded.enabled, mentions = excluded.mentions, challenges "
        "= excluded.challenges, frank = excluded.frank, replies = "
        "excluded.replies, updated_at = excluded.updated_at",
        (user_id, cur["enabled"], cur["mentions"], cur["challenges"],
         cur["frank"], cur["replies"],
         datetime.now(timezone.utc).isoformat()))
    return cur


# ------------------------------------------------------- subscriptions

def store_subscription(conn, user_id: int, endpoint: str,
                       p256dh: str, auth: str,
                       user_agent: str = "") -> None:
    """Insert or refresh one device subscription. An endpoint that
    shows up under a different member (shared browser profile) is
    re-homed to the latest subscriber."""
    now = datetime.now(timezone.utc).isoformat()
    conn.execute(
        "INSERT INTO push_subscriptions (user_id, endpoint, p256dh, "
        "auth, user_agent, created_at, last_seen_at) VALUES "
        "(?, ?, ?, ?, ?, ?, ?) ON CONFLICT(endpoint) DO UPDATE SET "
        "user_id = excluded.user_id, p256dh = excluded.p256dh, "
        "auth = excluded.auth, user_agent = excluded.user_agent, "
        "last_seen_at = excluded.last_seen_at",
        (user_id, endpoint, p256dh, auth, (user_agent or "")[:200],
         now, now))


def remove_subscription(conn, user_id: int, endpoint: str) -> None:
    conn.execute(
        "DELETE FROM push_subscriptions WHERE user_id = ? "
        "AND endpoint = ?", (user_id, endpoint))


def subscription_count(conn, user_id: int) -> int:
    row = conn.execute(
        "SELECT COUNT(*) AS n FROM push_subscriptions "
        "WHERE user_id = ?", (user_id,)).fetchone()
    return row["n"] if row else 0


def _subscriptions_for(conn, user_id: int) -> list[dict]:
    rows = conn.execute(
        "SELECT id, endpoint, p256dh, auth FROM push_subscriptions "
        "WHERE user_id = ?", (user_id,)).fetchall()
    return [dict(r) for r in rows]


def _frank_fan_ids(conn) -> list[int]:
    rows = conn.execute(
        "SELECT user_id FROM push_settings WHERE enabled = 1 "
        "AND frank = 1").fetchall()
    return [r["user_id"] for r in rows]


# ------------------------------------------------------------ sending

def _deduped(user_id: int, kind: str, ref: str) -> bool:
    key = (user_id, kind, ref)
    now = time.monotonic()
    with _recent_lock:
        last = _recent.get(key)
        if last is not None and now - last < _DEDUPE_WINDOW_S:
            return True
        _recent[key] = now
        if len(_recent) > 512:      # opportunistic sweep
            stale = [k for k, t in _recent.items()
                     if now - t >= _DEDUPE_WINDOW_S]
            for k in stale:
                _recent.pop(k, None)
    return False


def _deliver(db_path: Path, sub: dict, payload: dict) -> None:
    """One subscription send. Runs on the pool; prunes dead subs."""
    try:
        from pywebpush import WebPushException, webpush
        signer, _ = _vapid()
        if signer is None:
            return
        webpush(
            subscription_info={"endpoint": sub["endpoint"],
                               "keys": {"p256dh": sub["p256dh"],
                                        "auth": sub["auth"]}},
            data=json.dumps(payload),
            vapid_private_key=signer,
            vapid_claims={"sub": _subject()},
            ttl=3600, timeout=5)
    except Exception as exc:  # WebPushException or transport error
        status = getattr(getattr(exc, "response", None),
                         "status_code", None)
        if status in (404, 410):
            try:
                with get_conn(db_path) as conn:
                    conn.execute(
                        "DELETE FROM push_subscriptions WHERE id = ?",
                        (sub["id"],))
                    conn.commit()
            except Exception:
                pass
        else:
            log.info("web push send failed (status=%s): %s",
                     status, exc)


def _dispatch(db_path: Path, user_id: int, payload: dict) -> None:
    try:
        with get_conn(db_path) as conn:
            subs = _subscriptions_for(conn, user_id)
        for sub in subs:
            _POOL.submit(_deliver, db_path, sub, payload)
    except Exception:
        log.info("web push dispatch failed", exc_info=True)


def notify_user(db_path: Path, user_id: int, kind: str, title: str,
                body: str, url: str = "/chat", ref: str = "",
                online_ids=frozenset(), force: bool = False) -> None:
    """Push one member about one event. No-ops unless the member
    opted in (master + this kind), has a subscription, isn't
    currently in the room (they can see it live), and the same
    trigger hasn't just fired. The caller owns block / shadow-mute
    checks — by the time an event reaches here it is one the member
    is allowed to be told about. force=True (the settings "send a
    test" button) skips the presence + dedupe gates only."""
    try:
        if not configured():
            return
        if user_id in online_ids and not force:
            return
        with get_conn(db_path) as conn:
            settings = get_settings(conn, user_id)
            if not settings["enabled"]:
                return
            if kind in KINDS and not settings[kind]:
                return
            if subscription_count(conn, user_id) == 0:
                return
        if not force and _deduped(user_id, kind,
                                   ref or hashlib.sha1(
                                       body.encode()).hexdigest()[:12]):
            return
        payload = {"title": title, "body": body, "url": url,
                   "tag": f"hauntmap-{kind}",
                   "icon": "/static/img/icons/icon-192.png"}
        _dispatch(db_path, user_id, payload)
    except Exception:
        log.info("web push notify failed", exc_info=True)


def notify_frank_fans(db_path: Path, title: str, body: str,
                      url: str, online_ids=frozenset()) -> None:
    """Fan a Frank site announcement out to every opted-in member
    (kind 'frank'). The announcement path is already throttled
    (one shout per 10 min, six per hour), which doubles as this
    fan-out's dedupe."""
    try:
        if not configured():
            return
        with get_conn(db_path) as conn:
            targets = [uid for uid in _frank_fan_ids(conn)
                       if uid not in online_ids]
        for uid in targets:
            payload = {"title": title, "body": body, "url": url,
                       "tag": "hauntmap-frank",
                       "icon": "/static/img/icons/icon-192.png"}
            _dispatch(db_path, uid, payload)
    except Exception:
        log.info("web push frank fan-out failed", exc_info=True)
