"""HauntMap SMS text alerts — capture-first (Dan, Oct 22).

Pipeline: the site captures phone numbers NOW (status='captured'); actual
sending turns on only when Twilio credentials exist in the environment.
Nothing in this module ever fakes a send: without TWILIO_ACCOUNT_SID /
TWILIO_AUTH_TOKEN / TWILIO_FROM_NUMBER, send_sms() raises and callers fall
back to the captured state.

Pieces:
  * phone normalization to E.164 (US numbers)
  * 6-digit confirmation codes (form entry, or replying YES, confirms)
  * inbound webhook helpers (STOP / HELP / YES) + Twilio signature check
  * the matching engine: new pins -> per-subscriber digest, by ZIP-centroid
    radius or exact town, filtered by interest (haunts / events)

ZIP centroid dataset: app/zip_centroids.csv — ZIP Code Tabulation Area
(ZCTA) internal points (INTPTLAT/INTPTLONG) from the U.S. Census Bureau
Gazetteer file (Gaz_zcta_national), downloaded Oct 22, 2026 from
https://www2.census.gov/geo/docs/maps-data/data/gazetteer/Gaz_zcta_national.zip
Census Bureau data is public domain (17 U.S.C. 105 / census.gov terms).
"""
import base64
import csv
import hashlib
import hmac
import math
import os
import re
import secrets
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import quote

BASE_DIR = Path(__file__).resolve().parent
ZIP_CSV = BASE_DIR / "zip_centroids.csv"

TWILIO_SID = os.environ.get("TWILIO_ACCOUNT_SID", "")
TWILIO_TOKEN = os.environ.get("TWILIO_AUTH_TOKEN", "")
TWILIO_FROM = os.environ.get("TWILIO_FROM_NUMBER", "")

HAUNT_CATEGORIES = {"halloween", "haunted_houses", "christmas"}
EVENT_CATEGORIES = {"events"}

STOP_WORDS = {"STOP", "STOPALL", "UNSUBSCRIBE", "CANCEL", "END", "QUIT"}
YES_WORDS = {"YES", "Y", "START", "UNSTOP"}

SMS_SCHEMA = """
CREATE TABLE IF NOT EXISTS sms_subscribers (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    phone TEXT NOT NULL UNIQUE,
    zip TEXT, town TEXT, state TEXT,
    radius_miles INTEGER NOT NULL DEFAULT 15,
    interests TEXT NOT NULL DEFAULT 'both',
    consent_at TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'captured',
    confirm_code TEXT, confirm_expires TEXT,
    source TEXT, created_at TEXT NOT NULL, updated_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS sms_sends (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    subscriber_id INTEGER NOT NULL REFERENCES sms_subscribers(id),
    kind TEXT NOT NULL, body TEXT NOT NULL, pin_ids TEXT,
    twilio_sid TEXT, status TEXT NOT NULL DEFAULT 'queued',
    created_at TEXT NOT NULL
);
"""


def ensure_sms_tables(conn) -> None:
    """Idempotent — mirrors the lazy CREATE pattern used for town_requests,
    so endpoints work even on a DB init_db hasn't touched yet."""
    conn.executescript(SMS_SCHEMA)


def twilio_configured() -> bool:
    return bool(TWILIO_SID and TWILIO_TOKEN and TWILIO_FROM)


# ---------------------------------------------------------------- phones

def normalize_phone(raw: str) -> str | None:
    """US numbers only -> E.164 ('+1XXXXXXXXXX'), else None."""
    if not raw:
        return None
    digits = re.sub(r"\D", "", raw)
    if len(digits) == 11 and digits.startswith("1"):
        digits = digits[1:]
    if len(digits) != 10 or digits[0] in "01":
        return None
    return "+1" + digits


def new_confirm_code() -> str:
    return f"{secrets.randbelow(1_000_000):06d}"


def code_expiry(now: datetime | None = None) -> str:
    now = now or datetime.now(timezone.utc)
    return (now + timedelta(minutes=15)).isoformat()


def code_still_valid(expires_iso: str | None,
                     now: datetime | None = None) -> bool:
    if not expires_iso:
        return False
    try:
        exp = datetime.fromisoformat(expires_iso)
    except ValueError:
        return False
    if exp.tzinfo is None:
        exp = exp.replace(tzinfo=timezone.utc)
    return (now or datetime.now(timezone.utc)) <= exp


# ---------------------------------------------------------------- twilio

def send_sms(to_phone: str, body: str) -> str:
    """Send one SMS via the Twilio REST API. Returns the message SID.
    Raises RuntimeError when Twilio is not configured — never fakes it."""
    if not twilio_configured():
        raise RuntimeError("Twilio env vars not set — sending is disabled")
    import requests  # already a project dependency (see requirements.txt)
    resp = requests.post(
        f"https://api.twilio.com/2010-04-01/Accounts/{TWILIO_SID}/Messages.json",
        data={"From": TWILIO_FROM, "To": to_phone, "Body": body},
        auth=(TWILIO_SID, TWILIO_TOKEN),
        timeout=15,
    )
    resp.raise_for_status()
    return resp.json().get("sid", "")


def valid_twilio_signature(url: str, params: dict, signature: str) -> bool:
    """Twilio webhook signature: base64(HMAC-SHA1(auth_token,
    url + ''.join(key+value for sorted POST params)))."""
    if not TWILIO_TOKEN or not signature:
        return False
    payload = url + "".join(f"{k}{params[k]}" for k in sorted(params))
    mac = hmac.new(TWILIO_TOKEN.encode(), payload.encode(), hashlib.sha1)
    expected = base64.b64encode(mac.digest()).decode()
    return hmac.compare_digest(expected, signature)


CONFIRM_TEXT = (
    "HauntMap: your confirmation code is {code}. Enter it on the site to "
    "turn on text alerts for new haunts & events near you. "
    "Msg&data rates may apply. Reply STOP to end, HELP for help."
)

HELP_TEXT = (
    "HauntMap text alerts: new haunts & Halloween events near you, "
    "about 1 text/day max during the season. Reply STOP to end. "
    "Questions: gethauntmap@gmail.com"
)


# ---------------------------------------------------------------- geo

_zip_cache: dict[str, tuple[float, float]] | None = None


def zip_centroid(zip5: str) -> tuple[float, float] | None:
    global _zip_cache
    if _zip_cache is None:
        _zip_cache = {}
        try:
            with open(ZIP_CSV, newline="") as f:
                for row in csv.DictReader(f):
                    _zip_cache[row["zip"]] = (float(row["lat"]),
                                               float(row["lng"]))
        except FileNotFoundError:
            pass  # matching falls back to town-only for everyone
    return _zip_cache.get((zip5 or "").strip()[:5])


def haversine_miles(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    r = 3958.8
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlmb = math.radians(lon2 - lon1)
    a = (math.sin(dphi / 2) ** 2
         + math.cos(p1) * math.cos(p2) * math.sin(dlmb / 2) ** 2)
    return 2 * r * math.asin(math.sqrt(a))


def parse_city_state(town_label: str) -> tuple[str, str]:
    """'Morristown, NJ' -> ('Morristown', 'NJ'). Best-effort for the
    freeform town labels pins carry."""
    if not town_label:
        return "", ""
    parts = [p.strip() for p in town_label.split(",")]
    if len(parts) >= 2 and re.fullmatch(r"[A-Za-z]{2}", parts[-1]):
        return parts[0], parts[-1].upper()
    return parts[0], ""


# ---------------------------------------------------------------- matching

def interest_for_category(category: str) -> str | None:
    if category in HAUNT_CATEGORIES:
        return "haunts"
    if category in EVENT_CATEGORIES:
        return "events"
    return None


def subscriber_wants(sub: dict, interest: str) -> bool:
    pref = (sub.get("interests") or "both").lower()
    return pref == "both" or pref == interest


def match_pin(sub: dict, pin: dict) -> tuple[bool, str, float | None]:
    """Does this pin belong in this subscriber's digest?
    Returns (matched, human-readable reason, distance_miles_or_None)."""
    interest = interest_for_category(pin.get("category") or "")
    if interest is None:
        return False, f"pin category '{pin.get('category')}' is not a haunt/event category", None
    if not subscriber_wants(sub, interest):
        return False, f"subscriber wants '{sub.get('interests')}', pin is a {interest} pin", None

    pin_city, pin_state = parse_city_state(pin.get("town") or "")
    radius = sub.get("radius_miles")
    radius = 15 if radius is None else int(radius)

    if radius == 0:  # my town only
        same = (pin_city.lower() == (sub.get("town") or "").lower()
                and (not sub.get("state") or not pin_state
                     or pin_state == (sub.get("state") or "").upper()))
        if same:
            return True, f"town match ({pin_city}, {pin_state})", None
        return False, f"town-only subscriber; pin is in {pin_city}, {pin_state}", None

    centroid = zip_centroid(sub.get("zip") or "")
    plat, plng = pin.get("lat"), pin.get("lng")
    if centroid and plat is not None and plng is not None:
        dist = haversine_miles(centroid[0], centroid[1], float(plat), float(plng))
        if dist <= radius:
            return True, f"{dist:.1f} mi away (radius {radius})", dist
        return False, f"{dist:.1f} mi away — outside {radius} mi radius", dist
    # No coordinates on one side or the other: exact-town fallback.
    if pin_city and sub.get("town") and pin_city.lower() == sub["town"].lower():
        return True, "town match (no coordinates for distance check)", None
    return False, "no usable coordinates and towns differ", None


def build_digest(sub: dict, matched: list[dict]) -> str:
    """One text per subscriber per day, however many pins matched."""
    haunts = sum(1 for p in matched
                 if interest_for_category(p.get("category") or "") == "haunts")
    events = sum(1 for p in matched
                 if interest_for_category(p.get("category") or "") == "events")
    parts = []
    if haunts:
        parts.append(f"{haunts} new haunt{'s' if haunts != 1 else ''}")
    if events:
        parts.append(f"{events} event{'s' if events != 1 else ''}")
    town_label = ""
    if sub.get("town"):
        town_label = sub["town"] + (f", {sub['state']}" if sub.get("state") else "")
    elif matched:
        town_label = matched[0].get("town") or ""
    radius = sub.get("radius_miles")
    radius = 15 if radius is None else int(radius)
    if radius == 0:
        near = f"in {town_label}" if town_label else "in your town"
    else:
        near = (f"near {town_label} (within {radius} mi)" if town_label
                else f"within {radius} mi of you")
    link_town = town_label or "New Jersey"
    return (f"\U0001F383 {' + '.join(parts)} {near}: "
            f"gethauntmap.com/?town={quote(link_town)} — Reply STOP to end")


def select_digests(subscribers: list[dict], pins: list[dict]) -> list[dict]:
    """Pure matching pass — used by the dry-run and the sending job alike.
    Returns one dict per subscriber with >=1 matched pin."""
    out = []
    for sub in subscribers:
        matched, detail = [], []
        for pin in pins:
            ok, reason, dist = match_pin(sub, pin)
            detail.append({"pin_id": pin.get("id"), "matched": ok,
                           "reason": reason, "distance": dist})
            if ok:
                matched.append(pin)
        if matched:
            out.append({"subscriber": sub, "pins": matched,
                        "digest": build_digest(sub, matched),
                        "detail": detail})
    return out
