"""HauntMap v1 — mobile-first web app for sharing Halloween decorations.

Stack: FastAPI + Jinja2 + SQLite + local disk uploads. No user accounts in v1.
Voting is limited to one vote per browser per entry via cookie — this is a
SOFT limit only (cookies are trivially cleared); it stops casual double
voting, not determined abuse. See the vote route below.
"""
import asyncio
import calendar
import hashlib
import hmac
import ipaddress
import logging
import os
import queue
import re
import requests
import secrets
import shutil
import sqlite3
import subprocess
import tempfile
import threading
import uuid
import zipfile
import math
import random
import random
import json
import time
import urllib.request
import urllib.parse
from datetime import datetime, timedelta, timezone
from pathlib import Path

from fastapi import BackgroundTasks, FastAPI, Form, HTTPException, Query, Request, UploadFile, File, WebSocket, WebSocketDisconnect
from fastapi.responses import FileResponse, HTMLResponse, JSONResponse, RedirectResponse, Response, StreamingResponse
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from starlette.concurrency import run_in_threadpool
from starlette.middleware.gzip import GZipMiddleware
from PIL import Image, ImageOps, UnidentifiedImageError

from .db import (get_conn, init_db, add_entry_video, get_entry_videos,
                 set_entry_primary_video, tiktok_video_id)
from . import sms_alerts
from . import push as push_mod
from . import bracket as brk

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = Path(os.environ.get("DATA_DIR", BASE_DIR / "data"))
UPLOAD_DIR = Path(os.environ.get("UPLOAD_DIR", BASE_DIR / "uploads"))
THUMB_DIR = UPLOAD_DIR / "thumbs"
DB_PATH = DATA_DIR / "hauntmap.db"

SITE_NAME = os.environ.get("SITE_NAME", "HauntMap")
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "haunt-admin")

PHOTO_EXTS = {".jpg", ".jpeg", ".png", ".webp"}
VIDEO_EXTS = {".mp4"}
MAX_PHOTO_BYTES = 10 * 1024 * 1024
MAX_VIDEO_BYTES = 100 * 1024 * 1024
THUMB_MAX_WIDTH = 640
THUMB_W, THUMB_H = 800, 600  # feed thumbs: 4:3, the aspect every card renders at
# Item 10 (speed diet): feed-card variant of each thumb — 480x360, same
# filename in thumbs/card/, served at /media/thumbs/card/<name>. Phone
# cards render ~380px wide, so the 800px thumb was ~2x overserved.
CARD_THUMB_W, CARD_THUMB_H = 480, 360
CARD_THUMB_DIR = THUMB_DIR / "card"
ORIG_MAX_EDGE = 1920  # stored photo originals are capped at this long edge

CATEGORIES = ("halloween", "christmas", "halloween_stores", "restaurants", "coffee", "shops", "parks", "hotels", "ice_cream", "haunted_houses", "events", "live")
CAT_LABELS = {"halloween": "Halloween", "christmas": "Christmas",
              "halloween_stores": "Halloween Stores",
              "restaurants": "Restaurhaunts", "coffee": "Coffee & Cafes",
              "shops": "Shops", "parks": "Parks", "hotels": "Hotels",
              "ice_cream": "Ice Cream",
              "haunted_houses": "Haunted Houses",
              "events": "Events", "live": "Live Streams"}
CAT_EMOJI = {"halloween": "🎃", "christmas": "🎄", "halloween_stores": "👻",
             "restaurants": "🍽️", "coffee": "☕", "shops": "🛍️", "parks": "🌳",
             "hotels": "🏨", "ice_cream": "🍦",
             "haunted_houses": "🏚️", "events": "🎪", "live": "🔴"}

# Venue categories (Dan, Oct 25): food/drink/retail listings — the
# Restaurhaunts set (restaurants, coffee, shops) plus Halloween stores.
# Hotels joined Oct 27 (Dan): spooky/historic places to stay are Tour
# Fuel too — they extend a haunt tour like any other venue stop.
# Ice Cream joined Oct 27 (Dan): scoop shops are Tour Fuel too — a
# treat stop on the tour route, same venue treatment as hotels.
# Venues are tour stops, not haunts: their detail pages render no
# Scare-O-Meter and no haunt vote, and the vote/scare POST endpoints
# refuse venue entries server-side.
VENUE_CATS = ("restaurants", "coffee", "shops", "halloween_stores", "hotels", "ice_cream")

# Just-added ticker categories (Dan, Oct 26): the homepage "🆕 Just
# Added" crawl is reserved for new haunts + events only — halloween
# displays, haunted houses and events. Venue listings (the VENUE_CATS
# set), christmas, parks and live never appear in the ticker, however
# recent they are.
TICKER_CATS = ("halloween", "haunted_houses", "events")

# Events facets (Dan, Oct 22): /events is searchable by event type, music
# genre and venue style. Stored values stay short (they ride in URLs);
# a few get friendlier display labels in the dropdowns.
EVENT_TYPES = ("DJ Party", "Live Band", "Live Music", "Concert", "Bar Party",
               "Festival", "Parade", "Family Event", "Haunted Attraction Event",
               "Party", "Market")
EVENT_GENRES = ("EDM/Dance", "Hip-Hop", "Rock", "Jazz", "Latin", "Pop",
                "Classical/Piano", "Mixed/Open Format", "Spooky/Novelty")
EVENT_VENUES = ("Club", "Bar", "Rooftop", "Social Hall", "Ballroom/Event Space",
                "Theater", "Restaurant", "Outdoor", "Haunted Attraction", "Venue")
EVENT_TYPE_LABELS = {"Live Music": "Live Music (solo/duo)", "Party": "Party (general)",
                     "Market": "Market / Flea & Pop-Up"}
EVENT_VENUE_LABELS = {"Venue": "Venue (general)"}
EVENT_FACETS = (("type", "ev_type", EVENT_TYPES, EVENT_TYPE_LABELS),
                ("genre", "ev_genre", EVENT_GENRES, {}),
                ("venue", "ev_venue", EVENT_VENUES, EVENT_VENUE_LABELS))

# "Fall Family Fun" (Dan, Oct 27): a computed chip on /events for
# family-appropriate AND fall-flavored events. There is no stored
# facet for it — membership is derived per listed event from the facet
# fields plus title/tags/description text signals, so new postings
# sort themselves and nothing needs back-tagging. Family-safe is a
# hard gate: party/bar/club types and venues never qualify however
# fall-named, and neither do haunted attractions or adult-signalled
# titles (21+/18+, beer/wine/brewery, "horror(s)"). The fall signal
# and the family text signal read title+tags+description (the copy
# the posting pipeline writes from official pages); the family place
# signal (zoo, park, farm...) reads the title only, where the venue
# is named. The chip bar matches on the sentinel data-cat value
# FALL_FAMILY_FUN_VALUE — keep it in sync with the events.html JS.
FALL_FAMILY_FUN_VALUE = "__fff"
FALL_FAMILY_FUN_LABEL = "Fall Family Fun"
_FFF_FALL_RE = re.compile(
    r"(fall|harvest|pumpkin|corn\s*maze|orchard|apple|cider|hay\s?ride|"
    r"autumn|scarecrow|oktoberfest|trunk[\s-]?or[\s-]?treat|bonfire|"
    r"county fair)", re.I)
_FFF_FAMILY_RE = re.compile(
    r"(famil|kids?|children|all\s+ages|trunk[\s-]?or[\s-]?treat|youth|"
    r"toddler)", re.I)
_FFF_PLACE_RE = re.compile(
    r"\b(park|zoo|aquarium|museum|conservatory|arboretum|botanical|"
    r"library|farm|orchard)\b", re.I)
_FFF_ADULT_RE = re.compile(
    r"(21\s*\+|18\s*\+|adults?\s+only|\bbeer\b|\bwine\b|"
    r"\bbrewer(?:y|ies)\b|\bbrewpub\b|\bdistillery\b|\bhorrors?\b)", re.I)
_FFF_FAMILY_TYPES = ("Family Event", "Festival", "Parade")
_FFF_ADULT_TYPES = ("DJ Party", "Bar Party", "Party")
_FFF_ADULT_VENUES = ("Bar", "Club", "Rooftop")


def _is_fall_family_fun(e: dict) -> bool:
    """Computed 'Fall Family Fun' membership for one event row dict."""
    if e.get("ev_type") == "Haunted Attraction Event":
        return False
    title = e.get("title") or ""
    if e.get("ev_type") in _FFF_ADULT_TYPES \
            or e.get("ev_venue") in _FFF_ADULT_VENUES \
            or _FFF_ADULT_RE.search(title):
        return False
    text = " ".join([title, e.get("tags") or "",
                     e.get("description") or ""])
    family_side = e.get("ev_type") in _FFF_FAMILY_TYPES \
        or e.get("ev_venue") == "Outdoor" \
        or bool(_FFF_FAMILY_RE.search(text)) \
        or bool(_FFF_PLACE_RE.search(title))
    return family_side and bool(_FFF_FALL_RE.search(text))

app = FastAPI(title=SITE_NAME, docs_url=None, redoc_url=None)
templates = Jinja2Templates(directory=str(BASE_DIR / "templates"))
templates.env.globals["site_name"] = SITE_NAME

# In-memory admin sessions: token -> True. Resets on restart (fine for v1).
admin_sessions: set[str] = set()
ADMIN_COOKIE = "haunt_admin"


# Create dirs at import time: StaticFiles requires them to exist when mounted,
# which happens before the startup event runs.
DATA_DIR.mkdir(parents=True, exist_ok=True)
UPLOAD_DIR.mkdir(parents=True, exist_ok=True)
THUMB_DIR.mkdir(parents=True, exist_ok=True)
CARD_THUMB_DIR.mkdir(parents=True, exist_ok=True)


@app.on_event("startup")
def _startup() -> None:
    init_db(DB_PATH)
    _start_analytics_writer()
    # Fortification pass 2: prebuild the core hot aggregates, then let
    # the background refresher own their rebuilds (see the hot-cache
    # block). Warm failures never break boot — the cold-start fallback
    # in _ttl_cached builds on first request instead.
    _warm_hot_caches()
    _start_hot_refresher()
    try:
        _hauntsocial_boot()
    except Exception:
        # The mascot host is a courtesy layer — never break boot over it.
        logger.exception("HauntSocial boot (Frank ensure/backfill) failed")
    try:
        _apply_pin_coord_fixes()
    except Exception:
        # One-time data correction — never break boot over it.
        logger.exception("Pin coord fixes failed")


@app.on_event("shutdown")
def _shutdown() -> None:
    # Stop the hot-cache refresher (daemon thread; the stop event is
    # enough — no join, it never holds request state).
    _hot_stop.set()
    # Drain the analytics queue so a graceful deploy/restart loses no
    # page-view counts (the writer flushes what remains, then exits).
    _analytics_stop.set()
    if _analytics_thread is not None:
        _analytics_thread.join(timeout=10)


app.mount("/media", StaticFiles(directory=str(UPLOAD_DIR)), name="media")
app.mount("/static", StaticFiles(directory=str(BASE_DIR / "static")), name="static")


logger = logging.getLogger("hauntmap")

# Branded "down for construction" page (Dan, Oct 22): unhandled errors used to
# surface as a bare "Internal Server Error" (seen site-wide during the disk
# outage). The HTML lives in static/maintenance.html — fully self-contained
# (inline CSS, site-hosted font/logo) — and is loaded once here so the error
# path never depends on the template engine or the DB. The same file is
# reachable at /static/maintenance.html for an edge service to reuse.
try:
    _MAINTENANCE_HTML = (BASE_DIR / "static" / "maintenance.html").read_text(encoding="utf-8")
except OSError:  # pragma: no cover - file ships with the code
    _MAINTENANCE_HTML = "<h1>HauntMap is briefly down while we build something better. We'll be back soon!!</h1>"


@app.exception_handler(500)
@app.exception_handler(Exception)
async def _unhandled_error_page(request: Request, exc: Exception):
    """Log the real error server-side; show visitors the branded page.
    /api/* keeps the codebase's JSON error pattern."""
    logger.error("Unhandled error on %s %s", request.method, request.url.path,
                 exc_info=(type(exc), exc, exc.__traceback__))
    if request.url.path.startswith("/api/"):
        return JSONResponse({"error": "internal server error"}, status_code=500)
    return HTMLResponse(_MAINTENANCE_HTML, status_code=500,
                        headers={"Cache-Control": "no-store"})


@app.exception_handler(HTTPException)
async def _http_error(request: Request, exc: HTTPException):
    """HTTPExceptions keep FastAPI's default JSON shape — except 5xx, which
    gets the branded page like unhandled errors (all current raises are 4xx,
    so their behavior is unchanged)."""
    if exc.status_code >= 500:
        logger.error("HTTP %s on %s %s: %s", exc.status_code, request.method,
                     request.url.path, exc.detail)
        if request.url.path.startswith("/api/"):
            return JSONResponse({"error": "internal server error"}, status_code=exc.status_code)
        return HTMLResponse(_MAINTENANCE_HTML, status_code=exc.status_code,
                            headers={"Cache-Control": "no-store"})
    return JSONResponse({"detail": exc.detail}, status_code=exc.status_code,
                        headers=exc.headers)


@app.get("/healthz")
async def _healthz():
    """Render health-check target: DB-independent, 200 whenever the process
    is up, so a deploy only takes traffic once the new instance serves.
    Async on purpose (blip hardening, Oct 25): the answer is a constant
    built in memory on the event loop — it must never queue behind the
    thread pool or a database lock, which is how a busy-but-alive
    instance used to fail its health checks and get restarted."""
    return {"status": "ok"}


# ------------------------------------------------------- load shedding
# Wedge guardrail (Oct 25 incident): when more page renders are in
# flight than the single worker can chew through, extra page requests
# used to queue silently behind the threadpool until every route timed
# out (20+ minutes, healthz fine, nothing self-recovered). Now, past
# the render-slot limit, a page GET gets an immediate branded 503 with
# Retry-After instead of a queue slot: a brief "busy" page for a few
# visitors beats a total outage for everyone, in-flight renders finish
# at full speed instead of 40-way time-sliced, and the slots free up
# in seconds. /healthz, /api, /media, /static and /admin are NEVER
# shed — health checks, beacons, assets and Dan's admin access keep
# working at full saturation. Defined BEFORE the page-cache middleware
# so it runs INSIDE it: a cache HIT (a ~2ms dict lookup) never needs a
# render slot, only an actual render does.
_MAX_PAGE_RENDERS = int(os.environ.get("HAUNTMAP_MAX_PAGE_RENDERS", "24"))
_RENDER_SLOTS = threading.Semaphore(_MAX_PAGE_RENDERS)
_SHED_TOTAL = 0
_SHED_LAST_LOG = 0.0
_SHED_EXEMPT_PREFIXES = ("/healthz", "/api", "/media", "/static",
                         "/admin", "/favicon")


@app.middleware("http")
async def _shed_load(request: Request, call_next):
    global _SHED_TOTAL, _SHED_LAST_LOG
    if (request.method != "GET"
            or request.url.path.startswith(_SHED_EXEMPT_PREFIXES)):
        return await call_next(request)
    if not _RENDER_SLOTS.acquire(blocking=False):
        _SHED_TOTAL += 1
        now = time.monotonic()
        if now - _SHED_LAST_LOG > 30:
            _SHED_LAST_LOG = now
            logger.warning(
                "load shed: page render slots full (%d); %d requests "
                "shed so far this process", _MAX_PAGE_RENDERS, _SHED_TOTAL)
        return HTMLResponse(_MAINTENANCE_HTML, status_code=503,
                            headers={"Retry-After": "5",
                                     "Cache-Control": "no-store"})
    try:
        return await call_next(request)
    finally:
        _RENDER_SLOTS.release()


# ------------------------------------------------------------ perf: page cache
# In-app short-TTL cache for the two heaviest ANONYMOUS page renders
# (stability plan, Oct 24). The homepage and the events index run the
# site's most expensive queries; for a visitor carrying no state, the
# renders inside a short window are interchangeable, so repeat hits are
# served from memory instead of re-running the queries. Safety contract
# — a cached page must NEVER reach a request it wasn't rendered for:
#   * only GET, only the bare paths in PAGE_CACHE_PATHS, only with an
#     EMPTY query string — any parameter at all (town / sort / cat /
#     near / area / lat / lng / choose / type / genre / venue / state /
#     on / ...) bypasses;
#   * any cookie other than hm_sid bypasses. hm_sid is the analytics
#     id: set and read by _track_page_view (and read by the engaged-
#     time beacon); it never changes a render. Every other cookie in
#     this codebase is render state somewhere — haunt_admin (admin
#     session), hm_member (member session), tonight_last, voted_*,
#     scare_*, reported_*, hm_voter, costume_votes, fanart_votes,
#     hm_sms_pending — so its presence means "not the generic page";
#   * any Cloudflare location header _visitor_geo reads (cf-ipcity,
#     cf-ipregion, cf-ipregion-code, cf-iplatitude, cf-iplongitude)
#     bypasses: with the geo transform on, the homepage re-leads its
#     feed and Top-10 block by the visitor's area. (cf-ipcountry alone
#     is not a bypass trigger: behind Cloudflare it always arrives
#     WITH the headers above, and off-CF the GeoLite state fallback in
#     _visitor_geo can at most produce the state-level render, which
#     is the generic case this cache exists to serve.);
#   * an Authorization header bypasses; only 200 text/html is stored;
#   * Set-Cookie is never stored and never replayed (home() sets
#     tonight_last on its own response — that cookie goes only to the
#     visitor whose request earned the MISS).
# Defined FIRST so it runs INNERMOST of the http middlewares:
# _track_page_view still logs every hit (analytics + card view counts
# unaffected) and _cache_headers still owns media/static lifetimes.
# Known contract change, flagged for Dan: inside the TTL, Tonight's
# Display (a per-load random pick today) and the view counts printed
# on cards are shared/frozen — one pick serves every anonymous visitor
# until the entry expires. HAUNTMAP_PAGE_CACHE=off disables the cache.
PAGE_CACHE_PATHS = ("/", "/events")
PAGE_CACHE_TTL = float(os.environ.get("HAUNTMAP_PAGE_CACHE_TTL", "90"))
_PAGE_CACHE: dict[str, tuple[float, list, bytes]] = {}
_GEO_BYPASS_HEADERS = ("cf-ipcity", "cf-ipregion", "cf-ipregion-code",
                       "cf-iplatitude", "cf-iplongitude")
_STATELESS_COOKIES = frozenset({"hm_sid"})


def _page_cache_admits(request: Request) -> bool:
    if os.environ.get("HAUNTMAP_PAGE_CACHE", "on").lower() == "off":
        return False
    if request.method != "GET" or request.url.query:
        return False
    if request.headers.get("authorization"):
        return False
    if any(h in request.headers for h in _GEO_BYPASS_HEADERS):
        return False
    return not (set(request.cookies) - _STATELESS_COOKIES)


@app.middleware("http")
async def _page_cache(request: Request, call_next):
    if request.url.path not in PAGE_CACHE_PATHS:
        return await call_next(request)
    if not _page_cache_admits(request):
        response = await call_next(request)
        response.headers["X-Cache"] = "BYPASS"
        return response
    key = request.url.path
    entry = _PAGE_CACHE.get(key)
    if entry and entry[0] > time.monotonic():
        _, headers, body = entry
        return Response(content=body, status_code=200,
                        headers={**dict(headers), "X-Cache": "HIT"})
    response = await call_next(request)
    body = b"".join([chunk async for chunk in response.body_iterator])
    headers = [(k, v) for k, v in response.headers.items()
               if k.lower() not in ("set-cookie", "content-length")]
    out = Response(content=body, status_code=response.status_code,
                   headers={**dict(headers), "X-Cache": "MISS"})
    if (response.status_code == 200
            and response.headers.get("content-type", "").startswith("text/html")
            and len(body) <= 8 * 1024 * 1024):
        _PAGE_CACHE[key] = (time.monotonic() + PAGE_CACHE_TTL, headers, body)
    return out


@app.middleware("http")
async def _member_context(request: Request, call_next):
    """Expose the logged-in member to base.html so the header nav can
    turn its JOIN button into the member's @handle link (z125). Only
    requests carrying the member cookie pay the session lookup;
    everyone else renders the anonymous JOIN. Safe against the page
    cache above: its admission rule rejects any request with cookies
    beyond hm_sid, so member-rendered HTML is never stored or served
    to another visitor."""
    request.state.member = None
    if MEMBER_COOKIE in request.cookies:
        try:
            request.state.member = current_member(request)
        except Exception:
            request.state.member = None
    return await call_next(request)


@app.middleware("http")
async def _cache_headers(request: Request, call_next):
    """Cache lifetimes for file responses (stability plan, Oct 24;
    fortification pass 2, Oct 25).
    /media/ filenames are uuid4 hex on EVERY write path (public upload,
    admin media replace, costume / fan-art uploads, sponsor logos), and
    a replace mints a NEW name instead of overwriting — a media URL's
    bytes never change, so it earns a year + immutable.
    /static/ gets the same year; immutable ONLY when the URL carries
    the per-ship ?v= version stamp — a versioned URL's bytes can never
    change without the URL changing too. Unversioned /static/ keeps the
    plain year WITHOUT immutable: header art is referenced unversioned
    and HAS been swapped in place before (header_frank2.webp exists
    because the frank art was replaced) — immutable would pin
    superseded art in returning browsers for a year.
    Only 200s are stamped: a year-long header on a 404 would pin the
    absence — a /media/thumbs/card/ variant requested before its file
    is generated must be retryable once the file exists. HTML is
    untouched and stays fresh, as before."""
    response = await call_next(request)
    if response.status_code != 200:
        return response
    path = request.url.path
    if path.startswith("/media/"):
        response.headers["Cache-Control"] = "public, max-age=31536000, immutable"
    elif path.startswith("/static/"):
        if "v" in request.query_params:
            response.headers["Cache-Control"] = \
                "public, max-age=31536000, immutable"
        else:
            response.headers["Cache-Control"] = "public, max-age=31536000"
    return response


# ------------------------------------------------------- analytics writer
# Batched background writer for analytics rows (blip hardening, Oct 25).
# Diagnosis (Oct 24 outage): _track_page_view used to run a synchronous
# CREATE TABLE + ALTER attempts + INSERT + COMMIT on the event loop for
# EVERY page view, and the engagement loggers did the same per event.
# Under a traffic burst those writes serialized on the loop and on the
# SQLite write lock until health checks timed out and Render restarted
# the instance into a 502 cycle. Now the request path only enqueues an
# in-memory tuple (microseconds, never blocks); ONE daemon thread owns
# the analytics connection and flushes batches about once a second.
# Counts stay exact — batching delays a row by ~a second, and the
# shutdown hook drains the queue, so a graceful deploy loses nothing.
_ANALYTICS_FLUSH_SECONDS = 1.0
_ANALYTICS_BATCH_MAX = 500
_analytics_q: "queue.SimpleQueue[tuple]" = queue.SimpleQueue()
_analytics_stop = threading.Event()
_analytics_thread: threading.Thread | None = None


def _analytics_write_batch(conn, batch: list) -> None:
    pv = [r[1:] for r in batch if r[0] == "pv"]
    if pv:
        # Region source + IP fallback (Oct 27): a row's region normally
        # comes from Cloudflare's headers ('cf'). When the header
        # carried none — the zone's visitor-location transform is off,
        # so this is most rows today — the writer resolves the state
        # from the row's stored visitor IP against the bundled
        # GeoLite2 database ('ip'). Resolution lives HERE, on the
        # writer thread, never in the request path; a missing database
        # or library degrades silently to header-only geography.
        rows = []
        for r in pv:
            path_, ts_, ref_, dev_, sid_, country_, region_, city_, ua_ = r[:9]
            ip_addr = r[9] if len(r) > 9 else None
            geo_src = "cf" if region_ else None
            if ip_addr and (not region_ or not country_):
                ip_country, ip_state = _geoip_lookup(ip_addr)
                if ip_country:
                    if not country_:
                        country_ = ip_country
                    if not region_ and ip_country == "US" and ip_state:
                        region_ = ip_state
                        geo_src = "ip"
            rows.append((path_, ts_, ref_, dev_, sid_, country_, region_,
                         city_, ua_, ip_addr, geo_src))
        conn.executemany(
            "INSERT INTO page_views (path, viewed_at, referrer, device, sid, "
            "country, region, city, user_agent, ip_addr, geo_src) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)", rows)
    engaged = [r[1:] for r in batch if r[0] == "engaged"]
    if engaged:
        conn.executemany(
            "INSERT INTO engagement_events (created_at, event, path, seconds, sid, pvid) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            [(c, ENGAGED_EVENT, p, s, sid, (rest[0] if rest else None))
             for (c, s, p, sid, *rest) in engaged])
    engs = [r[1:] for r in batch if r[0] == "eng"]
    if engs:
        # Town is derived from the entry, as the old inline logger did —
        # resolved here, once per distinct entry in the batch.
        towns: dict = {}
        for _, _, entry_id, _src in engs:
            if entry_id and entry_id not in towns:
                row = conn.execute(
                    "SELECT town FROM entries WHERE id = ?", (entry_id,)).fetchone()
                towns[entry_id] = (
                    extract_city_state(row["town"] or "") or row["town"]) if row else None
        conn.executemany(
            "INSERT INTO engagement_events (created_at, event, entry_id, town, source) "
            "VALUES (?, ?, ?, ?, ?)",
            [(c, ev, eid, towns.get(eid), src) for (c, ev, eid, src) in engs])
    conn.commit()


def _analytics_writer() -> None:
    conn = None
    while True:
        try:
            first = _analytics_q.get(timeout=_ANALYTICS_FLUSH_SECONDS)
        except queue.Empty:
            if _analytics_stop.is_set():
                break  # queue drained and shutdown requested
            continue
        batch = [first]
        while len(batch) < _ANALYTICS_BATCH_MAX:
            try:
                batch.append(_analytics_q.get_nowait())
            except queue.Empty:
                break
        try:
            if conn is None:
                conn = get_conn(DB_PATH)
            _analytics_write_batch(conn, batch)
        except Exception:
            # Transient failure (e.g. lock contention beyond the busy
            # timeout): keep the rows — requeue and retry next flush
            # rather than dropping sponsor-facing counts.
            logger.exception("analytics flush failed; requeueing %d rows", len(batch))
            try:
                if conn is not None:
                    conn.close()
            except Exception:
                pass
            conn = None
            for item in batch:
                _analytics_q.put(item)
            time.sleep(1.0)
    if conn is not None:
        try:
            conn.close()
        except Exception:
            pass


def _start_analytics_writer() -> None:
    global _analytics_thread
    if _analytics_thread is None or not _analytics_thread.is_alive():
        _analytics_stop.clear()
        _analytics_thread = threading.Thread(
            target=_analytics_writer, name="analytics-writer", daemon=True)
        _analytics_thread.start()


def _device_bucket(ua: str) -> str:
    """Simple device detection from user agent (unchanged buckets)."""
    ua_lower = ua.lower()
    if "iphone" in ua_lower or "ipad" in ua_lower:
        return "iOS"
    if "android" in ua_lower:
        return "Android"
    if "windows" in ua_lower:
        return "Windows"
    if "macintosh" in ua_lower or "mac os" in ua_lower:
        return "Mac"
    if "linux" in ua_lower:
        return "Linux"
    return "Other"


# UA families for traffic breakdowns (Oct 27): page_views.user_agent is
# stored raw; this classifier is applied at REPORT time (machine-traffic
# breakdowns, sponsor-accuracy checks), never in the request path.
# Ordered most-specific first — search crawlers and preview fetchers
# also contain "bot", so they must win over the generic bot bucket.
_UA_FAMILY_RULES = (
    ("uptime_health", ("uptimerobot", "pingdom", "statuscake", "healthcheck",
                       "health-check", "render/", "kube-probe", "site24x7")),
    ("search_crawler", ("googlebot", "google-inspectiontool", "bingbot",
                        "duckduckbot", "baiduspider", "yandexbot", "applebot",
                        "petalbot", "seznambot", "naverbot")),
    ("social_preview", ("facebookexternalhit", "facebot", "twitterbot",
                        "whatsapp", "telegrambot", "discordbot", "slackbot",
                        "linkedinbot", "pinterestbot", "tiktok", "snapchat",
                        "skypeuripreview", "redditbot", "embedly", "iframely")),
    ("bot_scanner", ("bot", "spider", "crawler", "scraper", "curl", "wget",
                     "python-requests", "python-urllib", "go-http-client",
                     "headlesschrome", "scrapy", "libwww", "httpclient",
                     "okhttp", "axios", "node-fetch", "zgrab", "masscan")),
)


def _ua_family(ua: str | None) -> str:
    """Classify one stored User-Agent into a traffic family:
    'uptime_health', 'search_crawler', 'social_preview', 'bot_scanner',
    'browser' (a real browser UA), or 'other' (empty/unrecognized)."""
    if not ua:
        return "other"
    low = ua.lower()
    for family, needles in _UA_FAMILY_RULES:
        if any(n in low for n in needles):
            return family
    if "mozilla" in low and any(b in low for b in (
            "chrome", "safari", "firefox", "edg", "opr/", "samsungbrowser")):
        return "browser"
    return "other"


def _machine_ua_sql(column: str = "user_agent") -> tuple:
    """(sql_fragment, params): TRUE for rows whose stored User-Agent
    does NOT classify as a machine family under _UA_FAMILY_RULES — the
    report-time human screen for the traffic meta analysis (Oct 27),
    mirroring _ua_family exactly on the machine side (the needles are
    matched as substrings of the lowered UA, as the classifier does).
    Rows with no UA stored (everything before Oct 27's UA logging)
    pass: they cannot be UA-screened either way, and the admin page
    labels that instead of silently dropping the pre-UA era."""
    needles = sorted({n for _, ns in _UA_FAMILY_RULES for n in ns})
    likes = " OR ".join(f"lower({column}) LIKE ?" for _ in needles)
    return (f"({column} IS NULL OR NOT ({likes}))",
            tuple(f"%{n}%" for n in needles))


# Date the page_views geo columns started collecting (ship date of the
# geography panel) — the /admin stats page prints it so the breakdown
# is never mistaken for all-time coverage.
_GEO_COLLECTING_SINCE = "Oct 26, 2026"


def _pv_geo(request: Request) -> tuple:
    """Visitor geography for one page view, read straight off the
    request's Cloudflare headers (Dan, Oct 26 — powers the /admin
    'Visitors by geography' panel). cf-ipcountry rides every
    Cloudflare-proxied request; cf-ipregion / cf-ipregion-code /
    cf-ipcity arrive only once the zone's 'Add visitor location
    headers' managed transform is on (Dan's dashboard toggle). Absent
    or garbled = None — store only what the headers actually gave,
    never finer. US regions resolve to the state code the town data
    uses (via _state_code_from_region); other regions keep
    Cloudflare's region name verbatim."""
    h = request.headers
    country = (h.get("cf-ipcountry") or "").strip().upper()[:8] or None
    region_raw = (h.get("cf-ipregion") or "").strip()[:120]
    region = None
    if region_raw:
        region = region_raw
        if country == "US":
            region = _state_code_from_region(
                region_raw, h.get("cf-ipregion-code") or "") or region_raw
    city = (h.get("cf-ipcity") or "").strip()[:120] or None
    return country, region, city


# ------------------------------------------- IP state fallback (Oct 27)
# Dan's ask: which U.S. states are visiting. Cloudflare's region header
# only arrives with the zone's visitor-location transform, which is off
# (production rows carry country but ZERO region/city) — so page views
# also record the visitor's IP address (tracker table only, never
# displayed anywhere) and the analytics writer resolves the state from
# the bundled GeoLite2-City database (app/geoip/, MaxMind free edition
# — no external API calls, nothing leaves the server). State-level
# resolution for the admin stats table is all the address is used for.
_IP_GEO_COLLECTING_SINCE = "Oct 27, 2026"
_GEOIP_DB_PATH = Path(__file__).parent / "geoip" / "GeoLite2-City.mmdb"
_geoip_reader = None  # None = not tried yet, False = unavailable
_geoip_lock = threading.Lock()


def _geoip_lookup(ip: str) -> tuple:
    """(country_iso, us_state_code) for an IP or network address from
    the bundled GeoLite2-City database; (None, None) when the database
    or library is unavailable or the address isn't in it. Called only
    from the analytics writer thread."""
    global _geoip_reader
    if _geoip_reader is None:
        with _geoip_lock:
            if _geoip_reader is None:
                try:
                    import maxminddb
                    _geoip_reader = (maxminddb.open_database(
                        str(_GEOIP_DB_PATH)) if _GEOIP_DB_PATH.exists()
                        else False)
                except Exception:
                    _geoip_reader = False
    if not _geoip_reader:
        return None, None
    try:
        rec = _geoip_reader.get(ip)
    except Exception:
        return None, None
    if not rec:
        return None, None
    country = ((rec.get("country") or {}).get("iso_code")
               or "").strip().upper() or None
    state = None
    if country == "US":
        subs = rec.get("subdivisions") or []
        if subs:
            code = str(subs[0].get("iso_code") or "").strip().upper()
            if code.startswith("US-"):
                code = code[3:]
            if code in US_STATE_CODES:
                state = code
    return country, state


def _pv_ip(request: Request) -> str | None:
    """The visitor's IP address, canonicalized, for the writer's state
    lookup. The site sits behind Cloudflare, so the real visitor
    address is cf-connecting-ip; the first x-forwarded-for hop and the
    direct peer are fallbacks for non-proxied requests. Unparseable =
    None (nothing stored). String work only — this runs in the
    tracking middleware and must stay microseconds-cheap."""
    h = request.headers
    raw = (h.get("cf-connecting-ip") or "").strip()
    if not raw:
        raw = (h.get("x-forwarded-for") or "").split(",")[0].strip()
    if not raw and request.client:
        raw = request.client.host or ""
    try:
        return str(ipaddress.ip_address(raw))
    except ValueError:
        return None


@app.middleware("http")
async def _track_page_view(request: Request, call_next):
    """Log page views for the admin traffic dashboard. Skips static/media/admin, logged-in admin visits, and Jarvis's own verification checks.
    The row is enqueued for the batched analytics writer — this
    middleware never touches the database (blip hardening, Oct 25)."""
    response = await call_next(request)
    try:
        if request.method == "GET" and response.status_code == 200:
            path = request.url.path
            if not path.startswith(("/media", "/static", "/admin", "/favicon")):
                if request.cookies.get(ADMIN_COOKIE) not in admin_sessions and \
                   "HauntMap-Verify" not in request.headers.get("user-agent", ""):
                    referrer = request.headers.get("referer", "")[:500]
                    ua = request.headers.get("user-agent", "")[:500]
                    # Raw UA for the row (Oct 27 UA logging): stored at
                    # up to 512 chars so bot families can be told apart
                    # later; the device bucket above keeps its 500-char
                    # input and its buckets are unchanged.
                    ua_stored = request.headers.get("user-agent", "")[:512]
                    sid = request.cookies.get("hm_sid")
                    new_sid = not sid
                    if new_sid:
                        sid = secrets.token_hex(16)
                    country, region, city = _pv_geo(request)
                    _analytics_q.put((
                        "pv", path, datetime.now(timezone.utc).isoformat(),
                        referrer, _device_bucket(ua), sid,
                        country, region, city, ua_stored,
                        _pv_ip(request)))
                    if new_sid:
                        response.set_cookie("hm_sid", sid, max_age=30 * 24 * 3600,
                                            httponly=True, samesite="lax")
    except Exception:
        pass  # never break a page load for analytics
    return response


# Gzip for text responses (stability plan, Oct 24). Starlette's
# GZipMiddleware by default refuses image/video/audio/font/zip and
# event-stream content types, so media bytes are never re-compressed;
# HTML/CSS/JS/JSON/SVG shrink ~4-5x on the wire. Registered last so it
# wraps every other middleware, page-cache HITs included. Level 6:
# near-maximum ratio at a fraction of level 9's CPU on a 1-CPU box.
app.add_middleware(GZipMiddleware, minimum_size=1024, compresslevel=6)


# ---------------------------------------------------------------- helpers

def row_to_dict(row: sqlite3.Row) -> dict:
    d = dict(row)
    d["town_label"] = extract_city_state(d.get("town") or "") or d.get("town") or ""
    d["is_new"] = False
    if d.get("created_at"):
        try:
            created = datetime.fromisoformat(str(d["created_at"]).replace("Z", "+00:00"))
            if created.tzinfo is None:
                created = created.replace(tzinfo=timezone.utc)
            d["is_new"] = (datetime.now(timezone.utc) - created).days < 7
        except ValueError:
            pass
    if d["media_path"]:
        d["media_url"] = f"/media/{d['media_path']}"
        d["thumb_url"] = f"/media/{d['thumb_path']}" if d["thumb_path"] else d["media_url"]
    else:
        # media-less listings (events / halloween_stores)
        d["media_url"] = ""
        d["thumb_url"] = ""
    # Item 10: feed-card variant URL (480w). Server-side existence check:
    # the variant is used only when its file is actually on disk, else
    # the card falls back to the full thumb_url — a missing variant can
    # never produce a broken image. Card templates ALSO carry an
    # onerror swap to thumb_url as a second net. Detail-page hero
    # imagery keeps using thumb_url (full size) and never this field.
    d["thumb_card_url"] = d["thumb_url"]
    if d.get("thumb_path"):
        try:
            card_file = CARD_THUMB_DIR / Path(d["thumb_path"]).name
            if card_file.is_file():
                d["thumb_card_url"] = f"/media/thumbs/card/{card_file.name}"
        except OSError:
            pass
    return d


# Retention Wave 2, Item 7 (Dan, Oct 23): "views attract more views if
# we list them on all videos" — every listing-video surface shows its
# all-time detail-page view count, the SAME measure Trending and the
# leaderboard use: page_views rows on '/d/{id}' paths. One grouped
# query per handler (never per entry); templates render the count only
# when it is > 0, so a zero-view video never shows a count.
_VIEWS_GROUP_SQL = (
    "SELECT CAST(substr(path, 4) AS INTEGER) AS eid, COUNT(*) AS views "
    "FROM page_views WHERE path LIKE '/d/%' GROUP BY eid")


# ------------------------------------------------- hot-path TTL caches
# Wedge fix (Oct 25 incident, 13:30-13:52 ET): page renders were so
# CPU-heavy on the single worker (~0.5-0.9s each for / and /d/*) that a
# concurrency surge filled all 40 threadpool threads with renders;
# queued renders then starved every page route for 20+ minutes while
# the async /healthz kept answering. Root amplifier: several helpers
# rebuilt site-wide aggregates from scratch on EVERY render — a full
# GROUP BY scan of page_views (163k rows and growing), the Tonight's
# pool (entries scan + the same GROUP BY as a subquery + a row_to_dict
# and a filesystem stat per eligible pin), the per-category peer list
# (~5,800 row dicts + stats), and the town inventory. Those aggregates
# change slowly (view counts, town counts, eligibility), so they are
# now built at most once per TTL window and shared read-only; callers
# that annotate rows get shallow copies. Freshness impact is the same
# class the page cache already accepts (counts a minute or two stale).
#
# Fortification pass 2 (Oct 25): rebuilds no longer ride on visitor
# requests at all in steady state. Every builder registers itself in
# _HOT_BUILDERS, and a daemon refresher thread rebuilds each live
# aggregate just BEFORE its TTL expires, so a request only ever reads
# the latest snapshot. A request still builds synchronously in exactly
# two cases: cold start (no snapshot yet — the fallback that keeps the
# first request after a restart correct) and a snapshot grown older
# than 10x TTL, which can only happen if the refresher thread is dead
# or starved — rebuilding then is the self-healing choice. Between
# expiry and the refresher's next pass a request serves the current
# snapshot rather than queueing a rebuild onto the render path: under
# CPU overload (the wedge scenario) that trade is the whole point.
# Builders must be connection-free (open their own get_conn) and must
# capture nothing request-specific beyond what the cache key names —
# the refresher replays them on its own thread at any time.
_HOT_TTL = float(os.environ.get("HAUNTMAP_HOT_CACHE_TTL", "120"))
_HOT_REFRESH_SECONDS = float(os.environ.get("HAUNTMAP_HOT_REFRESH_SECONDS", "30"))
_TTL_CACHE: dict = {}
# RLock, not Lock: builders may compose other cached helpers (e.g.
# _trending's build reads _views_by_id), and a nested _ttl_cached on
# the same thread must not self-deadlock in the cold-build path.
_TTL_CACHE_LOCK = threading.RLock()
_HOT_BUILDERS: dict = {}
_hot_stop = threading.Event()
_hot_thread: threading.Thread | None = None


def _ttl_cached(key: str, build):
    """Return the shared snapshot for key, at most _HOT_TTL seconds
    old in steady state. See the block comment above for the exact
    contract (background refresh, serve-snapshot, cold-start and
    dead-refresher synchronous fallbacks)."""
    _HOT_BUILDERS[key] = build
    now = time.monotonic()
    hit = _TTL_CACHE.get(key)
    if hit is not None:
        hit[2] = now
        if hit[0] > now:
            return hit[1]
        if now - (hit[0] - _HOT_TTL) < _HOT_TTL * 10:
            return hit[1]
    with _TTL_CACHE_LOCK:
        hit = _TTL_CACHE.get(key)
        if hit is not None and hit[0] > time.monotonic():
            return hit[1]
        value = build()
        now = time.monotonic()
        _TTL_CACHE[key] = [now + _HOT_TTL, value, now]
        return value


def _hot_refresh_pass() -> None:
    """One refresher sweep: rebuild every live aggregate that is
    within one refresh interval of expiring; drop aggregates nobody
    has read in over two TTL windows (their next reader rebuilds
    synchronously, and the refresher stops paying for cold data)."""
    now = time.monotonic()
    for key, build in list(_HOT_BUILDERS.items()):
        hit = _TTL_CACHE.get(key)
        if hit is None:
            continue
        if now - hit[2] > 2 * _HOT_TTL + _HOT_REFRESH_SECONDS:
            with _TTL_CACHE_LOCK:
                _TTL_CACHE.pop(key, None)
            _HOT_BUILDERS.pop(key, None)
            continue
        if hit[0] - now > _HOT_REFRESH_SECONDS:
            continue
        try:
            value = build()
        except Exception:
            logger.exception("hot-cache refresh failed for %s", key)
            continue
        with _TTL_CACHE_LOCK:
            cur = _TTL_CACHE.get(key)
            last_access = cur[2] if cur is not None else now
            _TTL_CACHE[key] = [time.monotonic() + _HOT_TTL, value,
                               last_access]


def _hot_refresher() -> None:
    while not _hot_stop.is_set():
        try:
            _hot_refresh_pass()
        except Exception:
            logger.exception("hot-cache refresh pass failed")
        _hot_stop.wait(_HOT_REFRESH_SECONDS)


def _start_hot_refresher() -> None:
    global _hot_thread
    if _hot_thread is None or not _hot_thread.is_alive():
        _hot_stop.clear()
        _hot_thread = threading.Thread(
            target=_hot_refresher, name="hot-cache-refresher", daemon=True)
        _hot_thread.start()


def _warm_hot_caches() -> None:
    """Prebuild the core aggregates at boot (called from _startup,
    after init_db): the homepage + pin-page set whose rebuild cost
    caused the wedge, so the first visitor request after a restart
    reads snapshots instead of paying a cold build. A failure here
    must never break boot — the cold-start fallback in _ttl_cached
    covers anything left unbuilt."""
    try:
        with get_conn(DB_PATH) as conn:
            _views_by_id(conn)
            _category_rows("halloween")
            _town_inventory(conn, "halloween")
            _tonight_pool(conn, "halloween")
            _tonight_pool(conn, None)
            _trending()
    except Exception:
        logger.exception("hot-cache warm failed; cold-start fallback "
                         "will build on first request")


def _views_by_id(conn=None) -> dict:
    """All-time /d/{id} view counts by entry id. Callers only READ the
    dict (.get), so the shared cached instance is safe. The builder
    opens its own connection (the background refresher replays it);
    the conn argument is kept for call-site compatibility and ignored."""
    def build():
        with get_conn(DB_PATH) as c:
            return {r["eid"]: r["views"] for r in c.execute(_VIEWS_GROUP_SQL)}
    return _ttl_cached("views_by_id", build)


def _attach_views(conn, entries: list) -> list:
    """Set ``_views`` (all-time /d/{id} views, 0 when never viewed) on
    each entry dict, using a single grouped page_views query."""
    if not entries:
        return entries
    views = _views_by_id(conn)
    for e in entries:
        e["_views"] = views.get(e["id"], 0)
    return entries


# Rail Boost (Oct 25): one badge per rail card, priority ⭐ > 🔥 > NEW.
# ⭐ = Dan's featured/Top-10 picks (the is_featured column FEATURED_
# ENTRY_IDS enforces); 🔥 = the site's most-viewed pins — top 50 by
# all-time detail-page views with a 10-view floor so a young site never
# badges near-zero pins; NEW = posted within the last 7 days (row_to_
# dict's is_new). The badge rides on the pin dict as ``_badge`` and
# _pin_card.html renders it on rail cards only.
_HOT_BADGE_TOP_N = 50
_HOT_BADGE_MIN_VIEWS = 10


def _hot_view_ids(views: dict) -> set:
    ranked = sorted((v for v in views.values() if v > 0), reverse=True)
    if not ranked:
        return set()
    cutoff = max(ranked[min(len(ranked), _HOT_BADGE_TOP_N) - 1],
                 _HOT_BADGE_MIN_VIEWS)
    return {eid for eid, v in views.items() if v >= cutoff}


def _apply_card_badge(p: dict, hot_ids: set) -> None:
    if p.get("is_featured"):
        p["_badge"] = "star"
    elif p.get("id") in hot_ids:
        p["_badge"] = "hot"
    elif p.get("is_new"):
        p["_badge"] = "new"
    else:
        p["_badge"] = None


def haversine_miles(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    r = 3958.8  # earth radius in miles
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def geocode_nominatim(q: str) -> tuple[float, float] | None:
    """Geocode a place query via OpenStreetMap Nominatim. Returns (lat, lng) or None."""
    url = "https://nominatim.openstreetmap.org/search?" + urllib.parse.urlencode(
        {"q": q, "format": "json", "limit": 1})
    req = urllib.request.Request(url, headers={"User-Agent": "HauntMap/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode())
        if data:
            return float(data[0]["lat"]), float(data[0]["lon"])
    except Exception:
        pass
    return None


def get_entry(entry_id: int) -> dict | None:
    with get_conn(DB_PATH) as conn:
        row = conn.execute("SELECT * FROM entries WHERE id = ?", (entry_id,)).fetchone()
    return row_to_dict(row) if row else None


def _category_rows(category: str) -> list[dict]:
    """Every visible entry row in a category, as row dicts — the
    shared base set behind category_peers, _entries_with_views, the
    town page, /map, /nearby and the geo area feed (fortification
    pass 2, Oct 25). Building it costs a full category scan plus a
    row_to_dict (with a filesystem stat) per row, so it is TTL-cached
    and background-refreshed like the other hot aggregates; callers
    get shallow copies — the cached base rows are never mutated. A
    pin posted seconds ago can take up to _HOT_TTL seconds to appear
    in these derived views; its own page is unaffected."""
    def build():
        with get_conn(DB_PATH) as conn:
            rows = conn.execute(
                "SELECT * FROM entries WHERE hidden = 0 AND category = ?",
                (category,),
            ).fetchall()
        return [row_to_dict(r) for r in rows]
    base = _ttl_cached(f"rows:{category}", build)
    return [dict(p) for p in base]


def category_peers(entry: dict) -> list[dict]:
    """All other visible entries in the entry's category (row dicts),
    from the shared _category_rows snapshot."""
    return [p for p in _category_rows(entry["category"])
            if p["id"] != entry["id"]]


def nearest_pins(entry: dict, limit: int = 6) -> list[dict]:
    """Same-category pins nearest to `entry`, each annotated with `distance`
    in miles (haversine). Empty when the entry or all peers lack coords."""
    if entry.get("lat") is None or entry.get("lng") is None:
        return []
    scored = []
    for p in category_peers(entry):
        if p.get("lat") is None or p.get("lng") is None:
            continue
        p["distance"] = haversine_miles(entry["lat"], entry["lng"], p["lat"], p["lng"])
        scored.append(p)
    scored.sort(key=lambda p: (p["distance"], p["id"]))
    return scored[:limit]


# ---------------------------------------------------------------------------
# Retention Wave 1 (Oct 23): Item 3 video chain + Item 1 true "Near You".
# ---------------------------------------------------------------------------

# Item 3: sane radius for the video chain / "More videos near here" strip.
# Beyond this, a "next video" is not near in any useful sense and the pin
# page falls back to the plain geographic chain.
VIDEO_CHAIN_RADIUS_MI = 100.0

# Dan (Oct 25): "Near must mean visitable." The pin-page rails that
# select candidates by distance from the current pin — More near here,
# More haunts near this one (same pool), the More videos near here
# strip, and the /api/explore tail — take candidates ONLY within this
# cap. No radius expansion to fill slots: a sparse area shows a
# shorter rail, or none, and a rail's printed "within X mi" (the
# farthest card actually shown) can never exceed the cap. The video
# chain's own next-pick radius above is deliberately NOT this cap —
# the sticky Next bar chains exactly as before.
NEAR_RAIL_CAP_MI = 50.0


def has_footage(entry: dict) -> bool:
    """Footage predicate for the video chain (Item 3 spec): a TikTok
    /video/ URL or an uploaded video file. Deliberately narrower than the
    homepage "Has video" filter (any tiktok_url) — a live/profile TikTok
    link is not playable footage of the haunt."""
    tt = entry.get("tiktok_url") or ""
    return "/video/" in tt or entry.get("media_type") == "video"


# Restaurhaunts ordering (Dan, Oct 26): "Feature the Restaurants that
# most decked for Halloween first when using relocate for the user" —
# inside any location-scoped restaurant result set (the /restaurhaunts
# listing, /nearby with a restaurhaunt category, the pin-page near
# rails), the most Halloween-decked venues lead; location still scopes
# the set and the previous order (distance / recency) breaks ties.
# The score is computed ONLY from fields the entry already carries —
# no invented ratings:
#   +4  footage of the space (a TikTok URL or an uploaded video —
#       video proof of the decor; Al Chile is the archetype)
#   +2  per seasonal-decking term in title/description/tags
#       (Halloween pop-ups, decor, "decked out", spooky season…)
#   +1  per spooky-theming term in title/description/tags
#       (horror, haunted, ghost, vampire, coffin, gothic, skeleton,
#        witch, pumpkin, creepy, spooky)
_DECKED_SEASONAL_TERMS = (
    "halloween pop-up", "halloween popup", "halloween-themed",
    "halloween themed", "halloween menu", "halloween party",
    "halloween cocktail", "halloween drink", "spooky season",
    "decked", "decorat",
)
_DECKED_THEME_TERMS = (
    "horror", "haunted", "ghost", "vampire", "coffin", "gothic",
    "skeleton", "witch", "pumpkin", "creepy", "spooky",
)


def decked_score(entry: dict) -> int:
    """How decked-for-Halloween a restaurhaunt entry reads, from its
    own title / description / tags / media only (see the term lists
    above). Higher = more decked. Used purely as an ordering key for
    the restaurant lane (RESTAURHAUNT_CATS); never displayed."""
    text = " ".join(str(entry.get(k) or "") for k in
                    ("title", "description", "tags")).lower()
    score = 0
    if (entry.get("tiktok_url") or "").strip() \
            or entry.get("media_type") == "video":
        score += 4
    for term in _DECKED_SEASONAL_TERMS:
        if term in text:
            score += 2
    for term in _DECKED_THEME_TERMS:
        if term in text:
            score += 1
    return score


# Item 1: Cloudflare visitor-location headers. The site sits behind
# Cloudflare, whose "Add visitor location headers" managed transform can
# attach cf-ipcity / cf-ipregion / cf-ipcountry / cf-iplatitude /
# cf-iplongitude to every origin request. Whether that transform is
# enabled on Dan's zone is NOT verifiable from staging — every consumer
# below treats missing/garbled headers as "unknown" and falls back to
# today's behaviour. Deploy-day check: curl the live homepage with a
# known CF-PoP request (or inspect a real request's headers server-side)
# and confirm the Denver/Miami simulations below reproduce with real
# visitor headers.
_GEO_NEAR_RADIUS_MI = 100.0   # towns within this of the visitor point = near
_GEO_EXACT_FILL_RADIUS_MI = 75.0  # neighbours that join an exact-town anchor

# cf-ipregion arrives as a full name ("Colorado"); tests/tooling may send
# the 2-letter code instead. Map both to the state code used in town data.
_STATE_NAME_TO_CODE: dict[str, str] = {}


def _state_code_from_region(region: str, region_code: str = "") -> str:
    """Resolve a Cloudflare region value to a US state code, '' if unknown."""
    global _STATE_NAME_TO_CODE
    if not _STATE_NAME_TO_CODE:
        _STATE_NAME_TO_CODE = {name.lower(): code
                               for code, name in US_STATE_NAMES.items()}
        _STATE_NAME_TO_CODE["district of columbia"] = "DC"
        _STATE_NAME_TO_CODE["washington dc"] = "DC"
    for raw in (region_code, region):
        v = (raw or "").strip()
        if not v:
            continue
        if v.upper() in US_STATE_CODES:
            return v.upper()
        hit = _STATE_NAME_TO_CODE.get(v.lower())
        if hit:
            return hit
    return ""


def _visitor_geo(request: Request) -> dict | None:
    """Visitor's coarse area from Cloudflare headers, or None when the
    headers are absent/unusable (the staging + fallback case). Only the
    five documented headers are read (plus cf-ipregion-code when present,
    which some zones send alongside cf-ipregion). Non-US visitors get
    None: every mapped town is in the US, so geo cannot help them yet."""
    h = request.headers
    country = (h.get("cf-ipcountry") or "").strip().upper()
    if country and country != "US":
        return None
    city = (h.get("cf-ipcity") or "").strip()
    state = _state_code_from_region(h.get("cf-ipregion") or "",
                                    h.get("cf-ipregion-code") or "")
    if not state:
        # State-loyal near-me (Dan, Oct 27): the CF region headers only
        # arrive with the zone's visitor-location transform; when they
        # are absent the state still matters (it is the near-me default
        # boundary), so fall back to the bundled GeoLite2-City lookup
        # on the connecting IP — the same offline source the analytics
        # writer uses for its state table. US only, state granularity
        # only; a miss leaves the state unknown, never guessed.
        ip = _pv_ip(request)
        if ip:
            ip_country, ip_state = _geoip_lookup(ip)
            if ip_country == "US" and ip_state:
                state = ip_state
    lat = lng = None
    try:
        lat = float(h.get("cf-iplatitude") or "")
        lng = float(h.get("cf-iplongitude") or "")
        if not (-90 <= lat <= 90 and -180 <= lng <= 180):
            lat = lng = None
    except (TypeError, ValueError):
        lat = lng = None
    if not city and not state and lat is None:
        return None
    return {"city": city, "state": state, "lat": lat, "lng": lng}


def _states_opt_in(raw: str) -> bool:
    """The 'Include nearby states' opt-in (?states=1) shared by every
    near-me surface — the same values the Auto Tour toggle accepts.
    Absent/garbled = False: same-state is the default everywhere."""
    return (raw or "").strip().lower() in ("1", "true", "on", "yes")


def _town_inventory_uncached(conn, category: str = "halloween",
                             ev_type: str = "") -> list[dict]:
    """Every visible town in a category as {label, city, state, count,
    clat, clng} — the label/city/state come from the same extract_*
    helpers that build card town_labels, and the centroid is the mean of
    the town's pin coordinates (all halloween pins carry coords today).
    ev_type narrows the inventory to one event type (the /markets
    near-me resolution runs over Market entries only)."""
    inv: dict[str, dict] = {}
    query = ("SELECT town, lat, lng FROM entries "
             "WHERE hidden = 0 AND category = ?")
    params: list = [category]
    if ev_type:
        query += " AND ev_type = ?"
        params.append(ev_type)
    for r in conn.execute(query, params).fetchall():
        label = extract_city_state(r["town"] or "")
        if not label:
            continue
        t = inv.setdefault(label, {"label": label, "count": 0,
                                   "_lats": [], "_lngs": []})
        t["count"] += 1
        if r["lat"] is not None and r["lng"] is not None:
            t["_lats"].append(r["lat"])
            t["_lngs"].append(r["lng"])
    out = []
    for t in inv.values():
        t["city"] = extract_city(t["label"])
        t["state"] = extract_state(t["label"])
        t["clat"] = (sum(t["_lats"]) / len(t["_lats"])) if t["_lats"] else None
        t["clng"] = (sum(t["_lngs"]) / len(t["_lngs"])) if t["_lngs"] else None
        del t["_lats"], t["_lngs"]
        out.append(t)
    return out


def _town_inventory(conn=None, category: str = "halloween",
                    ev_type: str = "") -> list[dict]:
    """TTL-cached wrapper (wedge fix, Oct 25): the inventory rescans
    and re-aggregates every entry in the category; town counts and
    centroids change slowly, so builds are shared for _HOT_TTL
    seconds and background-refreshed (pass 2). Callers get shallow
    copies of the town dicts. The conn argument is kept for call-site
    compatibility; the builder opens its own connection."""
    def build():
        with get_conn(DB_PATH) as c:
            return _town_inventory_uncached(c, category, ev_type)
    base = _ttl_cached(f"towninv:{category}:{ev_type}", build)
    return [dict(t) for t in base]


def _resolve_visitor_area(inventory: list[dict], geo: dict | None,
                          multi: bool = False) -> dict:
    """Resolve the visitor's area against the town inventory.

    Resolution order (Item 1 spec):
      (a) exact town match — a mapped town whose city equals the header
          city (in the header state, when known);
      (b) nearest towns by haversine from the header lat/lng, within
          _GEO_NEAR_RADIUS_MI;
      (c) biggest towns in the visitor's state;
      (d) today's behaviour — biggest towns site-wide ("fallback").

    State-loyal default (Dan, Oct 27): when the visitor's state is
    known and the visitor has NOT opted into nearby states (multi —
    the module's "Include nearby states" toggle, ?states=1), the
    exact/near town sets are restricted to the visitor's OWN state:
    living <25 mi from NYC does not make an NJ visitor a New York
    visitor. multi=True restores the cross-state radius behaviour
    verbatim. A state with no in-radius supply falls through to (c);
    a state with no supply at all still lands in "nomap" below.
    A visitor whose area is known but has NO mapped supply at all (no
    exact/near/state town) resolves to mode "nomap": the module names
    their area honestly and shows the fallback towns rather than
    pretending New Jersey is near Denver (nearest mapped town to Denver
    is ~626 mi away in the Oct 23 snapshot).

    Returns {mode, area_name, heading, sub, chips, area_labels} where
    chips are the Near-you module's top-8 [{label, count}] and
    area_labels is the full set of town labels that count as "the
    visitor's area" for feed-leading (empty for fallback/nomap)."""
    biggest = sorted(inventory, key=lambda t: (-t["count"], t["label"]))
    fallback_chips = [{"label": t["label"], "count": t["count"]}
                      for t in biggest[:8]]
    base = {"mode": "fallback", "area_name": "",
            "heading": "Near you tonight",
            "sub": "The biggest haunt towns on the map right now — "
                   "tap yours, or jump straight to what's around you.",
            "chips": fallback_chips, "area_labels": set(),
            "state": "", "multi": multi}
    if not geo:
        return base
    city = (geo.get("city") or "").strip()
    state = geo.get("state") or ""
    vlat, vlng = geo.get("lat"), geo.get("lng")
    city_disp = _smart_case_city(city) if city else ""
    state_name = US_STATE_NAMES.get(state, state)
    # State-loyal default: a known state + no opt-in = own state only.
    loyal = bool(state) and not multi

    def chips_of(towns: list[dict]) -> list[dict]:
        return [{"label": t["label"], "count": t["count"]} for t in towns[:8]]

    def dist_to(t: dict, lat: float, lng: float) -> float | None:
        if t["clat"] is None or t["clng"] is None:
            return None
        return haversine_miles(lat, lng, t["clat"], t["clng"])

    # (a) exact town match
    exact = None
    if city:
        cands = [t for t in inventory if t["city"].lower() == city.lower()]
        if state:
            in_state = [t for t in cands if t["state"] == state]
            if in_state:
                cands = in_state
        if cands:
            exact = sorted(cands, key=lambda t: -t["count"])[0]
    if exact is not None and loyal and exact["state"] != state:
        # The header city and header state disagree across a state
        # line; under the state-loyal default the city anchor loses —
        # near/state resolution below speaks for the visitor's state.
        exact = None
    if exact is not None:
        alat = vlat if vlat is not None else exact["clat"]
        alng = vlng if vlng is not None else exact["clng"]
        neighbours: list[dict] = []
        if alat is not None and alng is not None:
            scored = []
            for t in inventory:
                if t["label"] == exact["label"]:
                    continue
                if loyal and t["state"] != state:
                    continue  # own state only — the toggle opts back in
                d = dist_to(t, alat, alng)
                if d is not None and d <= _GEO_EXACT_FILL_RADIUS_MI:
                    scored.append((d, t))
            neighbours = [t for _d, t in sorted(
                scored, key=lambda x: (x[0], -x[1]["count"], x[1]["label"]))]
        chips = [exact] + neighbours
        if len(chips) < 8 and state:
            have = {t["label"] for t in chips}
            for t in biggest:
                if len(chips) >= 8:
                    break
                if t["state"] == state and t["label"] not in have:
                    chips.append(t)
                    have.add(t["label"])
        area = {exact["label"]} | {t["label"] for t in neighbours}
        return {"mode": "exact",
                "area_name": f"{city_disp} area",
                "heading": f"Near You — {city_disp} area",
                "sub": (f"Closest haunt towns to {city_disp} in "
                        f"{state_name} first — tap a town to see its "
                        "haunts, or change your area." if loyal else
                        f"Closest haunt towns to {city_disp} first — "
                        "tap a town to see its haunts, or change your area."),
                "chips": chips_of(chips), "area_labels": area,
                "state": state, "multi": multi}
    # (b) nearest towns to the header coordinates
    if vlat is not None and vlng is not None:
        scored = []
        for t in inventory:
            d = dist_to(t, vlat, vlng)
            if d is not None and d <= _GEO_NEAR_RADIUS_MI:
                scored.append((d, t))
        if scored:
            ranked_all = [t for _d, t in sorted(
                scored, key=lambda x: (x[0], -x[1]["count"], x[1]["label"]))]
            near = ranked_all
            if loyal:
                # Own state only: an in-radius town across the line is
                # the toggle's business, not the default's. No in-state
                # town in radius = fall through to the state list (c).
                near = [t for t in near if t["state"] == state]
            if near:
                chips = list(near)
                if len(chips) < 8 and state:
                    have = {t["label"] for t in chips}
                    for t in biggest:
                        if len(chips) >= 8:
                            break
                        if t["state"] == state and t["label"] not in have:
                            chips.append(t)
                            have.add(t["label"])
                # Label rule: the header city can name the foreign
                # metro across the line (a Hackensack NJ fix resolving
                # as "New York City") — keep the header-city label
                # only when that city actually exists as a town in the
                # visitor's own state; otherwise label the module by
                # the visitor's nearest in-state town, never by the
                # foreign metro.
                label_city = city_disp
                if loyal and city_disp and not any(
                        t["state"] == state
                        and t["city"].lower() == city_disp.lower()
                        for t in inventory):
                    label_city = near[0]["city"]
                area_name = (f"{label_city} area" if label_city
                             else (state_name or "your area"))
                return {"mode": "near",
                        "area_name": area_name,
                        "heading": f"Near You — {area_name}",
                        "sub": (f"Closest haunt towns in {state_name} "
                                "first — tap a town to see its haunts, "
                                "or change your area."
                                if loyal and not city_disp else
                                f"Closest haunt towns to {area_name} in "
                                f"{state_name} first — tap a town to see "
                                "its haunts, or change your area."
                                if loyal else
                                f"Closest haunt towns to {area_name} "
                                "first — tap a town to see its haunts, or "
                                "change your area."),
                        "chips": chips_of(chips),
                        "area_labels": {t["label"] for t in near},
                        "state": state, "multi": multi}
    # (c) biggest towns in the visitor's state
    if state:
        in_state = [t for t in biggest if t["state"] == state]
        if in_state:
            return {"mode": "state",
                    "area_name": state_name,
                    "heading": f"Near You — {state_name}",
                    "sub": f"Biggest haunt towns in {state_name} — "
                           "tap a town to see its haunts, or change your area.",
                    "chips": chips_of(in_state),
                    "area_labels": {t["label"] for t in in_state},
                    "state": state, "multi": multi}
    # Known area, zero mapped supply: name it honestly, show fallback towns.
    if city or state:
        area_name = f"{city_disp} area" if city_disp else state_name
        return {"mode": "nomap",
                "area_name": area_name,
                "heading": f"Near You — {area_name}",
                "sub": f"No haunts mapped near {area_name} yet — add yours "
                       "or request your town below. Meanwhile, the biggest "
                       "haunt towns on the map:",
                "chips": fallback_chips, "area_labels": set(),
                "state": state, "multi": multi}
    return base


def _feed_has_video(e: dict) -> bool:
    """The homepage feed's "has video" predicate (same as the SQL
    video-first CASE in home()): any TikTok URL or an uploaded video file."""
    if (e.get("tiktok_url") or "").strip():
        return True
    return (e.get("media_path") or "").lower().endswith((".mp4", ".webm", ".mov"))


def _fetch_area_feed(cat: str, area_labels: set, scare: str, tag: str,
                     video: str, sort: str) -> list[dict]:
    """All pins of a category whose town label is in the visitor's area,
    honouring the feed's scare/tag/video filters and ordered exactly
    like the main feed (video-first, then the chosen sort). Used to lead
    the default feed with near-area pins (Item 1) — the caller merges
    these ahead of the regular feed and de-dupes, so the feed is never
    emptied, only re-led."""
    # Fortification pass 2: rows come from the shared _category_rows
    # snapshot instead of a per-render full category scan + row_to_dict
    # pass; the feed's scare/tag/video filters are applied as Python
    # predicates that mirror the old SQL exactly (the tag LIKE was a
    # wrapped-substring match over a fixed, wildcard-free tag list;
    # the video LIKEs were suffix matches on the lowered path).
    rows = _category_rows(cat)
    if scare in ("family", "spooky", "creepy", "terrifying", "extreme"):
        rows = [e for e in rows if e["scare_level"] == scare]
    if tag in ("animatronics", "inflatables", "handmade", "walkthrough",
               "projector", "lights", "music", "street-wide", "multi-house",
               "ticketed", "2025", "market", "oddities", "witchy", "craft",
               "flea", "free", "flagship", "21+"):
        rows = [e for e in rows
                if f",{tag}," in "," + (e["tags"] or "") + ","]
    if video.strip() == "1":
        rows = [e for e in rows
                if (e["tiktok_url"] or "").strip()
                or (e["media_path"] or "").lower().endswith(
                    (".mp4", ".webm", ".mov"))]
    with get_conn(DB_PATH) as conn:
        _attach_views(conn, rows)  # Item 7: area-led feed cards carry counts
    rows = [e for e in rows if e["town_label"] in area_labels]
    rows.sort(key=lambda e: e.get("created_at") or "", reverse=True)
    if sort == "top":
        rows.sort(key=lambda e: -(e.get("votes") or 0))
        rows.sort(key=lambda e: 0 if _feed_has_video(e) else 1)
    else:
        # Default (newest) view: hand-picked pins lead the area block,
        # newest hand-picked first — the same feed-order rule as the
        # main feed (Dan, Oct 23).
        rows.sort(key=lambda e: 0 if e.get("is_handpicked") else 1)
    return rows


# ---------------------------------------------------------------------------
# Retention Wave 3 (Oct 23): Item 5 "Tonight" layer — event-date parsing.
#
# Event pins carry their dates ONLY inside their titles, in the wild
# formats the seeding pipeline produced. parse_event_dates(title) pulls a
# (start, end) date span out of a title, or None when the title carries
# no usable date. It handles:
#   * ISO dates and ranges: "2026-10-23", "2026-09-26 to 2026-11-01"
#   * full ranges, shared or explicit years: "September 18 – November 8,
#     2026", "September 18 – November 1, 2026", "Oct 16 to Oct 18"
#   * short (same-month) ranges: "October 2–31, 2026", "Oct 9-10"
#   * single dates: "Saturday, October 31, 2026", "Oct 31", "Oct 31, 2026"
#   * date lists: "Oct 30 & 31, 2026", "Oct 23, 24, 30 & 31, 2026",
#     compound ranges "Oct 9-10, 16-17, 23-24, 2026"
#   * month-only spans: "October 2026", "All October 2026", "Nightly in
#     October" -> the whole month
# Approximations (documented, deliberate):
#   * Weekday qualifiers are IGNORED: "Fridays & Saturdays in October",
#     "Select Thursdays–Sundays, September 18 – November 1" count as on
#     EVERY day of the span. The alternative (parsing weekday sets per
#     title) would exclude most of the catalogue for a precision the
#     "on tonight" count does not need.
#   * Discrete date lists / compound ranges collapse to their spanning
#     interval (min date – max date): "Oct 17 and Oct 24" reads as
#     Oct 17–24. Same reasoning as the weekday rule.
#   * An end-only run ("Through Oct 31", "Weekends thru Oct 31") is
#     widened to start on the 1st of the end month — seasonal pop-ups and
#     farm runs that say "through" were running before the end date;
#     calling them single-day events would badly under-count.
#   * A yearless date belongs to the current season: the year of
#     "today" in America/New_York (titles are seeded for this season).
#   * Titles with NO date at all (in the Oct 23 snapshot: the Brooklyn
#     Halloween-day listings that carry only times like "10am-6:30pm",
#     plus "Fall Season" farm listings) return None and are EXCLUDED
#     from every "on tonight" count — never guessed onto Halloween day.
_EVENT_MONTHS = {
    "january": 1, "february": 2, "march": 3, "april": 4, "may": 5,
    "june": 6, "july": 7, "august": 8, "september": 9, "october": 10,
    "november": 11, "december": 12, "jan": 1, "feb": 2, "mar": 3,
    "apr": 4, "jun": 6, "jul": 7, "aug": 8, "sep": 9, "sept": 9,
    "oct": 10, "nov": 11, "dec": 12,
}
_EVENT_MONTH_RE = (r"(January|February|March|April|May|June|July|August|"
                   r"September|October|November|December|Jan|Feb|Mar|Apr|"
                   r"Jun|Jul|Aug|Sep|Sept|Oct|Nov|Dec)\.?")
_EVENT_PARSE_CACHE: dict = {}


def _today_et():
    """Today's date in America/New_York — the site's season clock.
    Never server-local: Render runs UTC, which flips the date at 8pm ET."""
    try:
        from zoneinfo import ZoneInfo
        return datetime.now(ZoneInfo("America/New_York")).date()
    except Exception:
        return datetime.now(timezone.utc).date()


def _mkdate(year: int, month: int, day: int):
    try:
        return datetime(year, month, day).date()
    except ValueError:
        return None


def _event_month_num(name: str) -> int:
    return _EVENT_MONTHS[name.lower().rstrip(".")]


def parse_event_dates(title: str):
    """(start, end) dates a title's event runs on, or None. See the
    Wave 3 banner above for formats + documented approximations."""
    if not title:
        return None
    cache_key = (title, _today_et().year)
    if cache_key in _EVENT_PARSE_CACHE:
        return _EVENT_PARSE_CACHE[cache_key]
    result = _parse_event_dates(title)
    _EVENT_PARSE_CACHE[cache_key] = result
    return result


def _parse_event_dates(title: str):
    s = (title.replace("\u2013", "-").replace("—", "-")
              .replace("\u2212", "-"))
    # ISO dates / ranges first (unambiguous).
    m = re.search(r"(\d{4})-(\d{2})-(\d{2})\s*(?:to|-)\s*"
                  r"(\d{4})-(\d{2})-(\d{2})", s)
    if m:
        a = _mkdate(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        b = _mkdate(int(m.group(4)), int(m.group(5)), int(m.group(6)))
        if a and b:
            return (a, b)
    m = re.search(r"(\d{4})-(\d{2})-(\d{2})", s)
    if m:
        a = _mkdate(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        if a:
            return (a, a)
    # Default year for yearless atoms: an explicit 202x year anywhere in
    # the title (film years like "(1981)" never match 202\d), else the
    # current season's year.
    years = re.findall(r"\b(202\d)\b", s)
    dyear = int(years[-1]) if years else _today_et().year

    atoms: list = []      # (start, end, position)
    consumed: list = []   # spans already claimed by range atoms

    def overlapped(span) -> bool:
        return any(span[0] < c[1] and c[0] < span[1] for c in consumed)

    def continuations(pos: int, month: int, year: int, anchor: int) -> None:
        """Bare-day list continuations right after a date atom:
        ", 24" / "& 31" / "and 24" / ", 16-17" / "& 30-Nov 1".
        Stops cold at anything that looks like a time or a price:
        a token followed by ':' or am/pm is a clock time, not a day."""
        while True:
            cm = re.match(
                r"\s*(?:,|&|\+|\band\b)\s*(\d{1,2})(?!\d)"
                r"(?:\s*-\s*(?:(\d{1,2})(?!\d)|" + _EVENT_MONTH_RE +
                r"\s+(\d{1,2})(?!\d)))?", s[pos:pos + 40], re.I)
            if not cm:
                return
            tail = s[pos + cm.end():pos + cm.end() + 4].lower().lstrip()
            if tail.startswith(("am", "pm")) or tail.startswith(":"):
                return
            d1 = _mkdate(year, month, int(cm.group(1)))
            if d1 is None:
                return
            if cm.group(2):
                d2 = _mkdate(year, month, int(cm.group(2)))
            elif cm.group(3):
                emonth = _event_month_num(cm.group(3))
                eyear = year + 1 if emonth < month else year
                d2 = _mkdate(eyear, emonth, int(cm.group(4)))
            else:
                d2 = d1
            if d2 is None:
                return
            atoms.append((d1, d2, anchor))
            pos += cm.end()

    # Full ranges: Month D - Month D (shared or explicit years, "-" or "to").
    for m in re.finditer(
            _EVENT_MONTH_RE + r"\s+(\d{1,2})(?!\d)(?:\s*,\s*(202\d))?"
            r"\s*(?:-|\bto\b)\s*" + _EVENT_MONTH_RE +
            r"\s+(\d{1,2})(?!\d)(?:\s*,\s*(202\d))?", s, re.I):
        y2 = (int(m.group(6)) if m.group(6)
              else (int(m.group(3)) if m.group(3) else dyear))
        y1 = int(m.group(3)) if m.group(3) else y2
        a = _mkdate(y1, _event_month_num(m.group(1)), int(m.group(2)))
        b = _mkdate(y2, _event_month_num(m.group(4)), int(m.group(5)))
        if a and b:
            atoms.append((a, b, m.start()))
            consumed.append(m.span())
            continuations(m.end(), b.month, b.year, m.start())
    # Short ranges: Month D-D / Month D to D.
    for m in re.finditer(
            _EVENT_MONTH_RE + r"\s+(\d{1,2})(?!\d)\s*(?:-|\bto\b)\s*"
            r"(\d{1,2})(?!\d)(?:\s*,\s*(202\d))?", s, re.I):
        if overlapped(m.span()):
            continue
        y = int(m.group(4)) if m.group(4) else dyear
        mo = _event_month_num(m.group(1))
        a = _mkdate(y, mo, int(m.group(2)))
        b = _mkdate(y, mo, int(m.group(3)))
        if a and b:
            atoms.append((a, b, m.start()))
            consumed.append(m.span())
            continuations(m.end(), mo, y, m.start())
    # Single dates: Month D [, YYYY] — the (?!\d) guard keeps a year from
    # being misread as a day ("October 2026" must NOT become October 20).
    for m in re.finditer(
            _EVENT_MONTH_RE + r"\s+(\d{1,2})(?!\d)(?:\s*,\s*(202\d))?",
            s, re.I):
        if overlapped(m.span()):
            continue
        y = int(m.group(3)) if m.group(3) else dyear
        mo = _event_month_num(m.group(1))
        a = _mkdate(y, mo, int(m.group(2)))
        if a:
            atoms.append((a, a, m.start()))
            consumed.append(m.span())
            continuations(m.end(), mo, y, m.start())

    if atoms:
        start = min(a[0] for a in atoms)
        end = max(a[1] for a in atoms)
        # End-only "through/thru/until <date>": one single-day atom that
        # the through-word directly introduces -> widen to the 1st of
        # that month (documented approximation above).
        tm = re.search(r"\b(?:through|thru|until)\b", s, re.I)
        if tm and start == end:
            first_pos = min(a[2] for a in atoms)
            if 0 <= first_pos - tm.end() <= 3:
                start = _mkdate(end.year, end.month, 1) or start
        return (start, end)
    # Month-only spans: a month name with no day attached anywhere
    # ("October 2026 evenings", "Nightly, October 2026", "in October").
    m = re.search(_EVENT_MONTH_RE + r"(?:\s+(202\d))?", s, re.I)
    if m:
        mo = _event_month_num(m.group(1))
        y = int(m.group(2)) if m.group(2) else dyear
        return (_mkdate(y, mo, 1),
                _mkdate(y, mo, calendar.monthrange(y, mo)[1]))
    return None


def event_on_date(title: str, on_date) -> bool:
    """True when a title's parsed span covers `on_date`. Undated titles
    (parse -> None) are never "on" — the honest exclusion, see banner."""
    span = parse_event_dates(title)
    return bool(span and span[0] <= on_date <= span[1])


def _event_start_minutes(title: str):
    """An event title's first start time as minutes past midnight, or
    None when the title carries no clock time. Handles
    '11:00 AM – 3:00 PM', '10am-6:30pm', '8pm' and the shared-meridiem
    range '7–11 PM' (a bare range start inherits the end's am/pm —
    the standard way these titles are written)."""
    if not title:
        return None
    s = title.replace("\u2013", "-").replace("—", "-")
    if re.search(r"\bnoon\s*-", s, re.I):
        return 12 * 60  # a range that starts at noon, e.g. 'noon-5pm'
    m = re.search(r"(\d{1,2})(?::(\d{2}))?\s*(am|pm)?\s*-\s*"
                  r"(\d{1,2})(?::(\d{2}))?\s*(am|pm)\b", s, re.I)
    if m:
        mer = (m.group(3) or m.group(6)).lower()
        hour = int(m.group(1)) % 12 + (12 if mer == "pm" else 0)
        return hour * 60 + int(m.group(2) or 0)
    m = re.search(r"(\d{1,2})(?::(\d{2}))?\s*(am|pm)\b", s, re.I)
    if m:
        mer = m.group(3).lower()
        hour = int(m.group(1)) % 12 + (12 if mer == "pm" else 0)
        return hour * 60 + int(m.group(2) or 0)
    return None


def _ev_day_label(d, today) -> str:
    """Section header for one by-day events section."""
    base = d.strftime("%A, %B ") + str(d.day)
    if d.year != today.year:
        base += d.strftime(", %Y")
    if d == today:
        return "Tonight — " + base
    if d == today + timedelta(days=1):
        return "Tomorrow — " + base
    return base


def _ev_sort_day(entries: list, sort: str) -> list:
    """Order inside one day section: by start time (timed events
    before untimed), then title. The Newest view puts the most
    recently added first, then start time / title."""
    def key(e):
        t = _event_start_minutes(e["title"])
        return (t is None, t or 0, (e["title"] or "").lower(), e["id"])
    out = sorted(entries, key=key)
    if sort == "new":
        out.sort(key=lambda e: e.get("created_at") or "", reverse=True)
    return out


def _events_on_count(conn, town_label: str, on_date) -> int:
    """Parsed events covering `on_date` whose town_label (the same
    extract_city_state label every card shows) equals `town_label`.
    Reads the TTL-cached by-town map (fortification pass 2); the
    empty-label case keeps the original direct scan so its semantics
    are byte-identical (the by-town map skips unparseable towns)."""
    if not town_label:
        n = 0
        for r in conn.execute(
                "SELECT title, town FROM entries "
                "WHERE hidden = 0 AND category = 'events'").fetchall():
            label = extract_city_state(r["town"] or "") or r["town"] or ""
            if label == town_label and event_on_date(r["title"], on_date):
                n += 1
        return n
    return _events_on_by_town(conn, on_date).get(town_label, 0)


def _events_on_by_town(conn=None, on_date=None) -> dict:
    """{town_label: count} of parsed events covering `on_date`, in one
    pass over the events category (the same labels _events_on_count
    matches against). TTL-cached per date (fortification pass 2):
    building it parses every event title's date span, and the Tonight
    strip paths asked for it — directly or via _next_events_day's
    14-day scan — on homepage and town renders. The date is part of
    the cache key, so the ET-midnight rollover is automatic. Callers
    only read the dict, so the shared instance is safe."""
    def build():
        counts: dict[str, int] = {}
        with get_conn(DB_PATH) as c:
            rows = c.execute(
                "SELECT title, town FROM entries "
                "WHERE hidden = 0 AND category = 'events'").fetchall()
        for r in rows:
            if event_on_date(r["title"], on_date):
                label = extract_city_state(r["town"] or "") or r["town"] or ""
                if label:
                    counts[label] = counts.get(label, 0) + 1
        return counts
    return _ttl_cached(f"evon:{on_date.isoformat()}", build)


def _next_events_day(conn, town_label: str, today, horizon: int = 14):
    """(date, count) of the first day AFTER today, within `horizon`
    days, on which `town_label` has a parsed event — None when the
    town has nothing coming up in the window."""
    for off in range(1, horizon + 1):
        day = today + timedelta(days=off)
        n = _events_on_count(conn, town_label, day)
        if n:
            return (day, n)
    return None


def _nearest_events_town(counts: dict, halloween_inv: list[dict],
                         vpoint) -> dict | None:
    """Nearest town with >= 1 event tonight, as {label, count} where
    count is the town's halloween display pins. Distance is haversine
    from `vpoint` (lat, lng) to the town centroid, capped at
    _GEO_NEAR_RADIUS_MI (the same "near" radius Item 1 uses); centroids
    come from the halloween inventory, filled from the events inventory
    for towns that have events but no display pins. Towns that also
    have display pins are preferred — the strip pairs the events count
    with a displays count, so a 0-display anchor reads as a dead end —
    but only when such a town is comparably near (within 25 mi, or
    twice the nearest distance, whichever is larger); otherwise the
    truly nearest events town wins. None when no town qualifies."""
    if not counts or vpoint is None:
        return None
    cents = {t["label"]: t for t in halloween_inv}
    if any(lbl not in cents for lbl in counts):
        with get_conn(DB_PATH) as conn:
            for t in _town_inventory(conn, "events"):
                cents.setdefault(t["label"], t)
    hw_counts = {t["label"]: t["count"] for t in halloween_inv}
    cands = []
    for label, n in counts.items():
        if n < 1:
            continue
        t = cents.get(label)
        if not t or t["clat"] is None or t["clng"] is None:
            continue
        d = haversine_miles(vpoint[0], vpoint[1], t["clat"], t["clng"])
        if d <= _GEO_NEAR_RADIUS_MI:
            cands.append((d, label))
    if not cands:
        return None
    cands.sort()
    nearest_d = cands[0][0]
    with_displays = [c for c in cands if hw_counts.get(c[1], 0) > 0]
    pick = cands[0]
    if with_displays and with_displays[0][0] <= max(25.0, 2 * nearest_d):
        pick = with_displays[0]
    return {"label": pick[1], "count": hw_counts.get(pick[1], 0)}


def _halloween_countdown(today) -> str:
    halloween = _mkdate(today.year, 10, 31)
    days = (halloween - today).days
    if days > 1:
        return f"\U0001F383 {days} days to Halloween"
    if days == 1:
        return "\U0001F383 1 day to Halloween"
    if days == 0:
        return "\U0001F383 It's Halloween night!"
    return "\U0001F383 Halloween night has passed — still lit tonight"


def _tonight_strip(town_label: str, displays: int, town_note: str = "",
                   events_day=None) -> dict:
    """Data for the _tonight_strip.html partial (Item 5): ET countdown,
    events near the anchor town, displays lit tonight. `displays` =
    halloween-category pins in the town (house displays run nightly
    through the season, so every display pin counts as lit).
    `events_day` counts events for a day other than today; the strip
    then names that day via events_when/events_iso instead of claiming
    the events are "on tonight" (used when the visitor's home town has
    nothing tonight but has an event coming up)."""
    today = _today_et()
    day = events_day or today
    with get_conn(DB_PATH) as conn:
        events_on = _events_on_count(conn, town_label, day)
    if day == today:
        events_when = "on tonight"
    else:
        events_when = "on " + day.strftime("%a, %b ") + str(day.day)
    return {"town_label": town_label, "town_note": town_note,
            "countdown": _halloween_countdown(today),
            "today_iso": today.isoformat(),
            "events_on": events_on, "displays": displays,
            "events_iso": day.isoformat(), "events_when": events_when,
            "scope": "town"}


def _tonight_strip_map() -> dict:
    """Map-wide variant of the Tonight strip, for visitors whose
    location is unknown: tonight's totals across the whole map, with
    no town presented as "near" them. (Dan, Oct 23: the strip used to
    anchor on the biggest town on the map — Staten Island — and show
    it to everyone next to the countdown.)"""
    today = _today_et()
    with get_conn(DB_PATH) as conn:
        counts = _events_on_by_town(conn, today)
        displays = conn.execute(
            "SELECT COUNT(*) AS n FROM entries "
            "WHERE hidden = 0 AND category = 'halloween'"
        ).fetchone()["n"]
    return {"town_label": "", "town_note": "",
            "countdown": _halloween_countdown(today),
            "today_iso": today.isoformat(),
            "events_on": sum(counts.values()), "displays": displays,
            "events_iso": today.isoformat(), "events_when": "on tonight",
            "scope": "map"}


def detail_chain(entry: dict) -> dict:
    """Loop data for a detail page: the nearest-pin chain (next + reciprocal
    prev), a 'More near here' rail and a 'More like this' rail, so no detail
    page is ever a dead end. All same-category; distances in miles."""
    peers = category_peers(entry)
    # Item 7: every peer carries its all-time view count (_views) so the
    # pin-card rails (More videos near here / More near here / More like
    # this / town rail) can show counts on video cards. One grouped
    # query for the whole chain, reused by the video-chain pick below.
    with get_conn(DB_PATH) as conn:
        _chain_views = _views_by_id(conn)
    for p in peers:
        p["_views"] = _chain_views.get(p["id"], 0)
    # Rail Boost: badge every peer once, here — all rails below (and the
    # sticky-bar / Next targets) read the same dicts.
    _hot_ids = _hot_view_ids(_chain_views)
    for p in peers:
        _apply_card_badge(p, _hot_ids)
    out = {"next_pin": None, "prev_pin": None, "more_near": [], "more_like": []}
    coord: list[dict] = []
    if entry.get("lat") is not None and entry.get("lng") is not None:
        coord = [p for p in peers
                 if p.get("lat") is not None and p.get("lng") is not None]
        for p in coord:
            p["distance"] = haversine_miles(
                entry["lat"], entry["lng"], p["lat"], p["lng"])
        coord.sort(key=lambda p: (p["distance"], p["id"]))
        # Near-rail cap (Dan, Oct 25): only visitable candidates —
        # within NEAR_RAIL_CAP_MI — however few that leaves. The full
        # `coord` list still drives the next/prev chain below, which
        # is geographic by design and unchanged.
        _near = [p for p in coord if p["distance"] <= NEAR_RAIL_CAP_MI]
        if entry.get("category") in RESTAURHAUNT_CATS:
            # Restaurhaunts ordering (Dan, Oct 26): inside the
            # location-scoped set, the most decked-for-Halloween
            # venues lead the rail; distance breaks ties. The
            # geographic next/prev chain below keeps using `coord`.
            _near.sort(key=lambda p: (-decked_score(p), p["distance"],
                                      p["id"]))
        out["more_near"] = _near[:6]
        out["next_pin"] = coord[0] if coord else None
        # Prev = the closest pin whose OWN nearest neighbour is this pin
        # (reciprocal nearest) — the step a chain-walker came from. Bounded
        # to the 40 closest candidates so the check stays cheap.
        if coord:
            # Wedge fix (Oct 25): same result, early exit. The entry is
            # cand's nearest neighbour iff NO other pin is at least as
            # close to cand as the entry is (a tie goes to the other
            # pin, exactly as the old full argmin scan resolved it —
            # the entry was scanned last and only a strictly smaller
            # distance replaced the incumbent). The old code ran the
            # full ~5,800-pin haversine scan for each of the 40
            # candidates (~230k haversines per pin-page render); most
            # candidates are now disqualified by one of their first
            # neighbours.
            for cand in coord[:40]:
                d_entry = haversine_miles(cand["lat"], cand["lng"],
                                          entry["lat"], entry["lng"])
                beaten = False
                for q in coord:
                    if q["id"] == cand["id"]:
                        continue
                    if haversine_miles(cand["lat"], cand["lng"],
                                       q["lat"], q["lng"]) <= d_entry:
                        beaten = True
                        break
                if not beaten:
                    out["prev_pin"] = cand
                    break
    # Retention Wave 1, Item 3 (video chain): when THIS pin has footage,
    # the primary Next target chains to ANOTHER pin with footage (same
    # predicate) instead of the nearest pin of any kind. The radius cap
    # keeps "near" honest — beyond it the caller falls back to the plain
    # geographic next above. WHICH footage pin leads the chain is the
    # most-viewed one (see the Dan note inside the block below).
    # (The old under-player "More videos near here" strip — `more_videos`
    # — was removed Oct 26 at Dan's order: his rail data showed it at
    # 23 seen / 0 clicks while the next-bar earned the clicks doing the
    # same job, so the next-bar is now the single video-continuation
    # path and "More near here" took the under-player slot.)
    out["next_video_pin"] = None
    out["video_chain"] = []
    out["town_centers"] = []
    if has_footage(entry):
        # `coord` is already distance-sorted and carries `distance`.
        vids = [p for p in coord
                if has_footage(p) and p["distance"] <= VIDEO_CHAIN_RADIUS_MI]
        # Dan (Oct 23, later the same day): "Play the most viewed
        # first" — and it should be based on the USER's location, like
        # everything else on the site. The pick is now the MOST-VIEWED
        # footage pin (all-time detail-page views, the Trending
        # measure), not the nearest:
        #   1. when the visitor's town is known, the detail template
        #      re-picks client-side from `video_chain` below — most-
        #      viewed footage pin within the radius of the VISITOR,
        #      using the same localStorage 'hm_town' signal Near You
        #      uses (the server never sees it, and the Cloudflare city
        #      header does not reach the app, so the browser is the
        #      only place this signal exists);
        #   2. the server-rendered default — most-viewed within the
        #      radius of THIS pin, distance breaking ties — is both
        #      the no-signal case and the fallback when no footage pin
        #      is near the visitor;
        #   3. if that pool is empty the caller keeps today's plain
        #      geographic next.
        views_by_id = _chain_views
        with get_conn(DB_PATH) as conn:
            inventory = _town_inventory(conn, entry["category"])
        if vids:
            out["next_video_pin"] = sorted(
                vids, key=lambda p: (-views_by_id.get(p["id"], 0),
                                     p["distance"], p["id"]))[0]
        # Client-side pool for the visitor-anchored re-pick: EVERY
        # footage peer with coordinates (the visitor may be nowhere
        # near this pin, so no radius cut here — the browser applies
        # the radius around the visitor instead).
        out["video_chain"] = [
            {"id": p["id"], "title": p["title"],
             "town_label": p.get("town_label") or "",
             "lat": p["lat"], "lng": p["lng"],
             "thumb_url": p.get("thumb_url") or "",
             # Rail Boost: distance from THIS pin, so the client-side
             # re-pick can keep the sticky bar's distance honest.
             "dist": p.get("distance"),
             "views": views_by_id.get(p["id"], 0)}
            for p in peers
            if has_footage(p) and p.get("lat") is not None
            and p.get("lng") is not None]
        out["town_centers"] = [
            [t["label"], t["city"], t["state"], t["clat"], t["clng"],
             t["count"]]
            for t in inventory
            if t["clat"] is not None and t["clng"] is not None]
    near_ids = {p["id"] for p in out["more_near"]}
    entry_tags = {t.strip() for t in (entry.get("tags") or "").split(",")
                  if t.strip()}

    def like_score(p):
        ptags = {t.strip() for t in (p.get("tags") or "").split(",") if t.strip()}
        return (1 if entry.get("scare_level")
                and p.get("scare_level") == entry["scare_level"] else 0,
                len(entry_tags & ptags), p.get("votes") or 0)

    pool = [p for p in peers if p["id"] not in near_ids]
    pool.sort(key=like_score, reverse=True)
    out["more_like"] = pool[:6]
    return out


_STATE_ZIP_RE = re.compile(r",\s*([A-Za-z]{2})(?:\s+\d{5}(?:-\d{4})?)?\s*$")
_STATE_ANY_RE = re.compile(
    r",\s*(NJ|NY|PA|MD|VA|MA|NH|CT|RI|DE|DC|VT|ME|NC|SC|GA|FL|TX|OH|IL|CA|WA|OR|"
    r"CO|AZ|NV|UT|MI|WI|MN|IA|MO|KS|NE|OK|AR|LA|MS|AL|TN|KY|IN|WV)\b")
US_STATE_CODES = {"NJ", "NY", "PA", "MD", "VA", "MA", "NH", "CT", "RI", "DE", "DC",
                  "VT", "ME", "NC", "SC", "GA", "FL", "TX", "OH", "IL", "CA", "WA",
                  "OR", "CO", "AZ", "NV", "UT", "MI", "WI", "MN", "IA", "MO", "KS",
                  "NE", "OK", "AR", "LA", "MS", "AL", "TN", "KY", "IN", "WV"}


def extract_state(town: str) -> str:
    """State code from a town field: 'Cranford, NJ', '22 Collins St, Cranford,
    NJ 07716', or the '…, NJ (notes)' form. '' when unparseable."""
    t = town or ""
    m = _STATE_ZIP_RE.search(t)
    if m:
        return m.group(1).upper()
    m = _STATE_ANY_RE.search(t)
    if m:
        return m.group(1).upper()
    parts = [p.strip() for p in t.split(",") if p.strip()]
    if len(parts) >= 2 and len(parts[-1]) <= 3:
        return parts[-1].upper()
    return ""


CITY_FIXES = {
    "port jefferson statiom": "Port Jefferson Station",
}


def _smart_case_city(city: str) -> str:
    """Normalize casing ('Massapequa park'/'MASSAPEQUA PARK' -> 'Massapequa
    Park') while leaving names with interior capitals (McLean, LaGrange) as-is."""
    if re.search(r"[a-z][A-Z]", city):
        return city

    small = {"of", "de", "the", "on", "at", "in"}

    def cap_word(w: str) -> str:
        pieces = []
        for p in w.split("'"):
            if p.lower().startswith("mc") and len(p) > 2:
                pieces.append("Mc" + p[2:3].upper() + p[3:].lower())
            else:
                pieces.append(p[:1].upper() + p[1:].lower())
        return "'".join(pieces)

    words = city.split(" ")
    return " ".join(
        w.lower() if (i > 0 and w.lower() in small) else cap_word(w)
        for i, w in enumerate(words)
    )


def extract_city(town: str) -> str:
    """Clean city name from a town field in any stored format."""
    t = town or ""
    m = _STATE_ZIP_RE.search(t) or _STATE_ANY_RE.search(t)
    if m:
        t = t[:m.start()]
    parts = [p.strip() for p in t.split(",") if p.strip()]
    city = parts[-1] if parts else t
    st = extract_state(town)
    if st and city.upper().endswith(" " + st):
        city = city[: -(len(st) + 1)].strip()
    city = " ".join(city.split())
    fix = CITY_FIXES.get(city.lower())
    if fix:
        return fix
    return _smart_case_city(city)


def extract_city_state(town: str) -> str:
    """'City, ST' label for any stored town format; '' for junk values."""
    city = extract_city(town)
    st = extract_state(town)
    if not city or city.upper() in US_STATE_CODES:
        return ""
    return f"{city}, {st}" if st else city


def states(category: str = "halloween") -> list[str]:
    """State codes present in a category. TTL-cached (fortification
    pass 2): it DISTINCT-scans every town string in the category and
    runs on the homepage's render path."""
    def build():
        with get_conn(DB_PATH) as conn:
            rows = conn.execute(
                "SELECT DISTINCT town FROM entries "
                "WHERE hidden = 0 AND category = ?",
                (category,),
            ).fetchall()
        seen: dict[str, None] = {}
        for r in rows:
            st = extract_state(r["town"])
            if st and st not in seen:
                seen[st] = None
        return sorted(seen)
    return list(_ttl_cached(f"states:{category}", build))


def towns(category: str = "halloween", state: str = "") -> list[str]:
    """'City, ST' labels present in a category (optionally one state).
    TTL-cached like states() above — same scan, same render paths."""
    def build():
        with get_conn(DB_PATH) as conn:
            rows = conn.execute(
                "SELECT DISTINCT town FROM entries "
                "WHERE hidden = 0 AND category = ? ORDER BY town",
                (category,),
            ).fetchall()
        seen: dict[str, None] = {}
        for r in rows:
            if state and extract_state(r["town"]) != state.upper():
                continue
            city_state = extract_city_state(r["town"])
            if city_state and city_state not in seen:
                seen[city_state] = None
        return sorted(seen)
    return list(_ttl_cached(f"towns:{category}:{state}", build))


# Display names for the /admin geography panel: Cloudflare's
# cf-ipcountry is a bare ISO code. Common codes get a friendly name;
# anything unlisted renders as its code (never a guessed name).
# 'XX' is Cloudflare's own "country unknown" value.
_COUNTRY_NAMES = {
    "US": "United States", "CA": "Canada", "MX": "Mexico", "GB": "United Kingdom",
    "IE": "Ireland", "DE": "Germany", "FR": "France", "ES": "Spain",
    "IT": "Italy", "NL": "Netherlands", "BE": "Belgium", "CH": "Switzerland",
    "AT": "Austria", "SE": "Sweden", "NO": "Norway", "DK": "Denmark",
    "FI": "Finland", "PL": "Poland", "PT": "Portugal", "GR": "Greece",
    "CZ": "Czechia", "HU": "Hungary", "RO": "Romania", "UA": "Ukraine",
    "RU": "Russia", "TR": "Türkiye", "IL": "Israel", "AE": "UAE",
    "SA": "Saudi Arabia", "IN": "India", "PK": "Pakistan", "BD": "Bangladesh",
    "CN": "China", "JP": "Japan", "KR": "South Korea", "TW": "Taiwan",
    "HK": "Hong Kong", "SG": "Singapore", "MY": "Malaysia", "TH": "Thailand",
    "VN": "Vietnam", "PH": "Philippines", "ID": "Indonesia", "AU": "Australia",
    "NZ": "New Zealand", "BR": "Brazil", "AR": "Argentina", "CL": "Chile",
    "CO": "Colombia", "PE": "Peru", "ZA": "South Africa", "NG": "Nigeria",
    "EG": "Egypt", "KE": "Kenya", "PR": "Puerto Rico", "XX": "Unknown",
}

US_STATE_NAMES = {
    "NJ": "New Jersey", "NY": "New York", "PA": "Pennsylvania", "MD": "Maryland",
    "VA": "Virginia", "MA": "Massachusetts", "NH": "New Hampshire", "CT": "Connecticut",
    "RI": "Rhode Island", "DE": "Delaware", "DC": "Washington, DC", "VT": "Vermont",
    "ME": "Maine", "NC": "North Carolina", "SC": "South Carolina", "GA": "Georgia",
    "FL": "Florida", "TX": "Texas", "OH": "Ohio", "IL": "Illinois", "CA": "California",
    "WA": "Washington", "OR": "Oregon", "CO": "Colorado", "AZ": "Arizona", "NV": "Nevada",
    "UT": "Utah", "MI": "Michigan", "WI": "Wisconsin", "MN": "Minnesota", "IA": "Iowa",
    "MO": "Missouri", "KS": "Kansas", "NE": "Nebraska", "OK": "Oklahoma", "AR": "Arkansas",
    "LA": "Louisiana", "MS": "Mississippi", "AL": "Alabama", "TN": "Tennessee",
    "KY": "Kentucky", "IN": "Indiana", "WV": "West Virginia",
    # Canada opens (Dan, Oct 27): provinces resolve through the same
    # region-name map so a Canadian pin's board/tabs read properly.
    "BC": "British Columbia",
}

# Region tabs shown after the state tabs in the homepage bottom place row,
# in the row's long-standing curated order.
REGION_TABS = [("long-island", "Long Island"), ("manhattan", "Manhattan"),
               ("brooklyn", "Brooklyn"), ("queens", "Queens"), ("bronx", "Bronx"),
               ("staten-island", "Staten Island"), ("boston", "Boston"),
               ("dc-area", "DC Area")]


def _region_terms(region: str) -> list[str]:
    if region in METRO_TERMS:
        return METRO_TERMS[region]
    if region in BOROUGH_TERMS:
        return BOROUGH_TERMS[region]
    if region == "long-island":
        return LONG_ISLAND_TERMS
    return []


def _place_tabs(cat: str, cur_state: str, cur_region: str, sort: str,
                scare: str, tag: str, video: str) -> list[dict]:
    """Bottom-of-homepage place tabs (Dan, Oct 22: update the cities at the
    bottom of the page): every state the current category actually covers,
    biggest first, plus the curated region shortcuts — each with its LIVE pin
    count, computed from the same rows and predicates the feed filter uses,
    so the row refreshes itself as pins come and go."""
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT town FROM entries WHERE hidden = 0 AND category = ?",
            (cat,),
        ).fetchall()
    base = f"/?cat={cat}"
    if sort != "top":
        base += f"&sort={sort}"
    if scare:
        base += f"&scare={scare}"
    if tag:
        base += f"&tag={tag}"
    if video:
        base += "&video=1"
    lowers: list[str] = []
    state_counts: dict[str, int] = {}
    for r in rows:
        t = r["town"] or ""
        lowers.append(t.lower())
        st = extract_state(t)
        if st:
            state_counts[st] = state_counts.get(st, 0) + 1
    tabs = [{"label": "All", "href": base, "count": len(rows),
             "active": not cur_state and not cur_region}]
    for code in sorted(state_counts,
                       key=lambda c: (-state_counts[c], US_STATE_NAMES.get(c, c))):
        tabs.append({"label": US_STATE_NAMES.get(code, code),
                     "href": f"{base}&state={code}",
                     "count": state_counts[code],
                     "active": cur_state == code and not cur_region})
    for slug, label in REGION_TABS:
        terms = _region_terms(slug)
        n = sum(1 for lt in lowers if any(term in lt for term in terms))
        if n:
            tabs.append({"label": label, "href": f"{base}&region={slug}",
                         "count": n, "active": cur_region == slug})
    return tabs


def is_admin(request: Request) -> bool:
    return request.cookies.get(ADMIN_COOKIE) in admin_sessions


def safe_ext(filename: str) -> str:
    return Path(filename or "").suffix.lower()


def save_upload(upload: UploadFile, max_bytes: int) -> Path:
    """Stream an upload to a temp file, enforcing max_bytes. Returns temp path."""
    tmp = UPLOAD_DIR / f"tmp-{uuid.uuid4().hex}"
    size = 0
    with tmp.open("wb") as f:
        while chunk := upload.file.read(1024 * 256):
            size += len(chunk)
            if size > max_bytes:
                f.close()
                tmp.unlink(missing_ok=True)
                raise ValueError(f"File too large (limit {max_bytes // (1024*1024)} MB).")
            f.write(chunk)
    return tmp


def _crop_43(im: Image.Image) -> Image.Image:
    """Center-crop to 4:3 — the aspect every card/duel/leader image renders at
    (the browser was downloading full portrait frames and cropping client-side)."""
    w, h = im.size
    target = 4 / 3
    if w / h > target:
        nw = int(h * target)
        x = (w - nw) // 2
        return im.crop((x, 0, x + nw, h))
    nh = int(w / target)
    y = (h - nh) // 2
    return im.crop((0, y, w, y + nh))


def _exif_orientation(im: Image.Image) -> int:
    """EXIF Orientation tag (274); 1 = upright. 1 when absent/unreadable."""
    try:
        return int(im.getexif().get(274) or 1)
    except Exception:
        return 1


def _save_pixels(im: Image.Image, dest: Path, fmt: str) -> None:
    """Save already-transposed pixels WITHOUT any EXIF orientation flag,
    so no viewer can rotate the image a second time."""
    im.info.pop("exif", None)
    if fmt == "JPEG":
        im.convert("RGB").save(dest, "JPEG", quality=85, optimize=True)
    elif fmt == "PNG":
        im.save(dest, "PNG", optimize=True)
    elif fmt == "WEBP":
        im.save(dest, "WEBP", quality=85)
    else:
        im.save(dest, fmt)


def _normalize_orientation(src: Path) -> bool:
    """Physically rotate a stored photo's pixels per its EXIF orientation
    flag, then strip the flag (Dan Oct 22: pictures must ALWAYS display
    right side up). Browsers honor the flag inconsistently — some ignore
    it and show the raw (sideways) pixels — so the pixels themselves must
    be upright. Returns True when the file was rewritten."""
    if src.suffix.lower() not in PHOTO_EXTS:
        return False
    try:
        with Image.open(src) as im:
            im.load()
            if _exif_orientation(im) == 1:
                return False
            fmt = im.format or "JPEG"
            upright = ImageOps.exif_transpose(im)
        tmp = src.with_suffix(src.suffix + ".upr")
        _save_pixels(upright, tmp, fmt)
        tmp.replace(src)
        return True
    except (OSError, UnidentifiedImageError):
        return False


def _write_thumb(im: Image.Image, dest: Path) -> None:
    im = _crop_43(ImageOps.exif_transpose(im).convert("RGB"))
    if im.width > THUMB_W:
        im = im.resize((THUMB_W, THUMB_H), Image.LANCZOS)
    im.save(dest, "JPEG", quality=76, optimize=True)


def make_card_variant(thumb_dest: Path) -> None:
    """Item 10: write the 480x360 feed-card variant for a thumb that
    was just (re)generated, at thumbs/card/<same filename>. Guarded:
    a variant failure must NEVER break an upload or a rethumb — the
    card templates fall back to the full thumb when no variant file
    exists, so skipping is always safe."""
    try:
        CARD_THUMB_DIR.mkdir(parents=True, exist_ok=True)
        dest = CARD_THUMB_DIR / thumb_dest.name
        with Image.open(thumb_dest) as im:
            im.load()
            im = ImageOps.exif_transpose(im).convert("RGB")
            if im.size != (CARD_THUMB_W, CARD_THUMB_H):
                im = im.resize((CARD_THUMB_W, CARD_THUMB_H), Image.LANCZOS)
            im.save(dest, "JPEG", quality=76, optimize=True)
    except (OSError, UnidentifiedImageError):
        pass


def _cap_original(src: Path) -> None:
    """Downscale an oversized stored original in place (detail pages serve the
    original; phone photos arrive at 3-5 MB). No-op when already small enough."""
    try:
        with Image.open(src) as im:
            im.load()
            rotated = _exif_orientation(im) != 1
            im = ImageOps.exif_transpose(im)
            if max(im.size) <= ORIG_MAX_EDGE and not rotated:
                return
            fmt = im.format or "JPEG"
            if max(im.size) > ORIG_MAX_EDGE:
                im.thumbnail((ORIG_MAX_EDGE, ORIG_MAX_EDGE), Image.LANCZOS)
            _save_pixels(im, src, fmt)
    except (OSError, UnidentifiedImageError):
        pass


def _recompress_jpeg(src: Path) -> None:
    """Re-encode a byte-fat JPEG in place at q85, same dimensions (some phones
    write ~q97: a 960x1440 frame at 1.8 MB). Only when >500 KB and smaller."""
    try:
        if src.suffix.lower() not in (".jpg", ".jpeg") or src.stat().st_size <= 500_000:
            return
        tmp = src.with_suffix(".rejpg")
        with Image.open(src) as im:
            im.load()
            ImageOps.exif_transpose(im).convert("RGB").save(
                tmp, "JPEG", quality=85, optimize=True)
        if tmp.stat().st_size < src.stat().st_size:
            tmp.replace(src)
        else:
            tmp.unlink(missing_ok=True)
    except (OSError, UnidentifiedImageError):
        pass


def make_thumb(src: Path, dest_name: str) -> str:
    """Create a JPEG thumbnail for a photo. Returns the relative thumb path."""
    rel = f"thumbs/{dest_name}_thumb.jpg"
    dest = THUMB_DIR / f"{dest_name}_thumb.jpg"
    _normalize_orientation(src)  # stored original's pixels upright, flag stripped
    _cap_original(src)
    _recompress_jpeg(src)
    with Image.open(src) as im:
        _write_thumb(im, dest)
    make_card_variant(dest)
    return rel


def make_video_poster(src: Path, dest_name: str) -> str | None:
    """Extract a poster frame from a video for feed thumbnails.
    Returns the relative thumb path, or None if ffmpeg is unavailable/fails."""
    rel = f"thumbs/{dest_name}_poster.jpg"
    dest = THUMB_DIR / f"{dest_name}_poster.jpg"
    try:
        subprocess.run(
            ["ffmpeg", "-y", "-i", str(src), "-ss", "1", "-vframes", "1",
             "-vf", f"scale={THUMB_W}:-1", str(dest)],
            capture_output=True, timeout=30, check=True,
        )
        try:  # normalize the poster to the same 4:3/q76 spec as photo thumbs
            with Image.open(dest) as im:
                im.load()
                _write_thumb(im, dest)
        except (OSError, UnidentifiedImageError):
            pass
        make_card_variant(dest)
        return rel
    except (subprocess.SubprocessError, OSError):
        return None


# ---------------------------------------------------------------- public pages

def _tonight_pool_uncached(conn, category: str | None) -> list[dict]:
    """Eligible Tonight's Display pins: real media only (an uploaded photo,
    or a TikTok / uploaded video that has a thumbnail), never DUEL-excluded
    pins (stock photos, 2025 entries), never 2025-tagged. Each dict carries
    _views (detail-page views from page_views) and _has_video."""
    cat_sql = "AND e.category = ?" if category else ""
    params = [category] if category else []
    rows = conn.execute(
        f"""SELECT e.*, COALESCE(v.views, 0) AS _views,
              CASE WHEN (e.tiktok_url IS NOT NULL AND TRIM(e.tiktok_url) != '')
                        OR e.media_type = 'video' THEN 1 ELSE 0 END AS _has_video
            FROM entries e
            LEFT JOIN (SELECT CAST(substr(path, 4) AS INTEGER) AS eid,
                              COUNT(*) AS views
                       FROM page_views WHERE path LIKE '/d/%' GROUP BY eid) v
              ON v.eid = e.id
            WHERE e.hidden = 0 {cat_sql}
              AND e.media_path IS NOT NULL AND TRIM(e.media_path) != ''
              AND (e.media_type = 'photo'
                   OR (e.thumb_path IS NOT NULL AND TRIM(e.thumb_path) != ''))
              AND NOT (',' || COALESCE(e.tags, '') || ',') LIKE '%,2025,%'
            ORDER BY e.id""", params).fetchall()
    return [d for d in (row_to_dict(r) for r in rows)
            if d["id"] not in DUEL_EXCLUDE_IDS]


def _tonight_pool(conn=None, category: str | None = None) -> list[dict]:
    """TTL-cached wrapper (wedge fix, Oct 25): building the pool runs
    an entries scan plus the page_views GROUP BY as a subquery plus a
    row_to_dict (with a filesystem stat) per eligible pin — and the
    homepage builds it on every render, twice over (Tonight's pick +
    Daily Fright). The pool's membership and view counts are shared
    for _HOT_TTL seconds and background-refreshed (pass 2); the
    per-load random pick is unaffected (picks are taken from the pool
    fresh each load, as before). Callers get shallow copies. The conn
    argument is kept for call-site compatibility; the builder opens
    its own connection."""
    def build():
        with get_conn(DB_PATH) as c:
            return _tonight_pool_uncached(c, category)
    base = _ttl_cached(f"tonight:{category}", build)
    return [dict(d) for d in base]


def _tonight_quality_pool(conn) -> list[dict]:
    """The Tonight's Display quality pool, shared by the random
    homepage pick and Item 6's deterministic daily pick so the two can
    never drift: eligible pins (see _tonight_pool) that have video,
    plus the 200 most-viewed eligible pins, ordered by id."""
    rows = _tonight_pool(conn, "halloween")
    if not rows:
        rows = _tonight_pool(conn, None)
    if not rows:
        return []
    quality = {r["id"]: r for r in rows if r["_has_video"]}
    for r in sorted(rows, key=lambda r: (-r["_views"], r["id"]))[:200]:
        quality.setdefault(r["id"], r)
    return [quality[k] for k in sorted(quality)]


def _pick_tonights_display(conn, exclude_id=None) -> dict | None:
    """Tonight's Display: a fresh random pick on every homepage load
    (Dan, Oct 22 — supersedes the earlier date-seeded daily pick). Pool
    rules unchanged: eligible halloween pins that have video, plus the
    200 most-viewed eligible pins (by detail-page views), real media
    only. exclude_id (the visitor's previous pick, from the tonight_last
    cookie) is skipped when the pool has more than one entry, so a
    reload doesn't serve the same pin twice in a row."""
    pool = _tonight_quality_pool(conn)
    if not pool:
        return None
    pool_size = len(pool)
    if exclude_id is not None and pool_size > 1:
        narrowed = [r for r in pool if r["id"] != exclude_id]
        if narrowed:
            pool = narrowed
    pick = dict(random.choice(pool))
    pick.pop("_views", None)
    pick.pop("_has_video", None)
    pick["_pool_size"] = pool_size
    return pick


def _daily_display(conn, et_date) -> dict | None:
    """Item 6 (Daily Fright): the canonical display drop for one
    America/New_York date. SAME pool as Tonight's Display (the shared
    _tonight_quality_pool over _tonight_pool), but the pick is
    date-seeded and deterministic — every visitor, every load, all day
    gets the same pin, and it rotates at ET midnight when et_date
    rolls. (Tonight's Display itself stays a per-load random pick, per
    Dan Oct 22; the daily drop is deliberately a different contract:
    one drop a TikTok post can deep-link to.)"""
    pool = _tonight_quality_pool(conn)
    if not pool:
        return None
    pick = dict(random.Random(et_date.toordinal()).choice(pool))
    pick.pop("_views", None)
    pick.pop("_has_video", None)
    return pick


def _trending() -> list[dict]:
    """Homepage Trending strip: the 5 most-viewed media-carrying pins
    site-wide (detail-page views DESC, votes DESC, id — the ranking
    the old inline LEFT JOIN in home() produced), zero-view pins
    excluded. TTL-cached + background-refreshed (fortification
    pass 2): the old query re-ran the page_views GROUP BY plus a
    media-entries scan on EVERY homepage render. Callers get copies."""
    def build():
        with get_conn(DB_PATH) as conn:
            rows = [row_to_dict(r) for r in conn.execute(
                "SELECT * FROM entries WHERE hidden = 0 "
                "AND media_path IS NOT NULL AND TRIM(media_path) != ''"
            ).fetchall()]
        views = _views_by_id()
        for d in rows:
            d["_views"] = views.get(d["id"], 0)
        rows.sort(key=lambda d: (-d["_views"], -(d["votes"] or 0), d["id"]))
        return [d for d in rows[:5] if d["_views"] > 0]
    return [dict(d) for d in _ttl_cached("trending", build)]


def _category_counts() -> dict:
    """Visible-entry count per category ({category: n}). TTL-cached +
    background-refreshed (fortification pass 2): /restaurhaunts and
    /media-kit both GROUP BY'd the whole entries table per render for
    numbers that move only when a pin is posted."""
    def build():
        with get_conn(DB_PATH) as conn:
            return {r["category"]: r["n"] for r in conn.execute(
                "SELECT category, COUNT(*) AS n FROM entries "
                "WHERE hidden = 0 GROUP BY category").fetchall()}
    return dict(_ttl_cached("catcounts", build))


# Region term lists for the homepage feed filters (boston/dc-area metros,
# NYC boroughs, Long Island). Shared by the home() filter branches and the
# bottom place-tabs counter so the two can never drift apart.
METRO_TERMS = {
            "boston": ["boston", "somerville", "cambridge", "medford", "malden",
                       "quincy", "brookline", "weymouth", "braintree", "saugus",
                       "lynn", "revere", "winthrop", "arlington, ma", "newton, ma",
                       "belmont, ma", "watertown, ma", "melrose, ma", "stoneham, ma",
                       "woburn, ma", "chelsea, ma", "everett, ma", "milton, ma",
                       "dedham, ma", "burlington, ma"],
            "dc-area": ["washington, dc", "district of columbia", "alexandria",
                        "arlington, va", "silver spring", "bethesda", "potomac",
                        "chevy chase", "falls church", "mclean", "vienna",
                        "rockville", "kensington", "takoma park", "springfield, va",
                        "annandale", "fairfax", "reston", "herndon", "sterling",
                        "ashburn", "chantilly", "centreville", "hyattsville"],
        }

BOROUGH_TERMS = {
            "staten-island": ["staten island"],
            "brooklyn": ["brooklyn"],
            "manhattan": ["manhattan", "new york, ny"],
            "queens": ["queens"],
            "bronx": ["bronx"],
        }

LONG_ISLAND_TERMS = ["wantagh", "bellmore", "merrick", "levittown", "east meadow", "malverne",
                    "massapequa", "seaford", "farmingdale", "bethpage", "hicksville", "plainview",
                    "syosset", "huntington", "babylon", "lindenhurst", "deer park", "brentwood",
                    "smithtown", "commack", "melville", "wyandanch", "west babylon", "north babylon",
                    "copiague", "amityville", "freeport", "baldwin", "oceanside", "rockville centre",
                    "hempstead", "uniondale", "roosevelt", "garden city", "mineola", "new hyde park",
                    "great neck", "port washington", "roslyn", "albertson", "williston park",
                    "floral park", "franklin square", "west hempstead", "elamont", "valley stream",
                    "lynbrook", "east rockaway", "hewlett", "woodmere", "cedarhurst", "inwood",
                    "lawrence", "far rockaway", "long beach", "island park", "oceanside",
                    "bay shore", "brightwaters", "islandia", "hauppauge", "central islip",
                    "east islip", "west islip", "islip", "oakdale", "sayville", "patchogue",
                    "bellport", "mastic", "shirley", "moriches", "center moriches", "east moriches",
                    "manorville", "calverton", "riverhead", "jamesport", "mattituck", "cuthogue",
                    "southold", "greenport", "orient", "shelter island", "sag harbor", "easthampton",
                    "southampton", "bridgehampton", "watermill", "montauk", "amgansett", "wainscott",
                    "north haven", "north sea", "nantucket", "nantucket"]


@app.get("/", response_class=HTMLResponse)
def home(request: Request, sort: str = "new", town: str = "", town_search: str = "",
         state: str = "", region: str = "", cat: str = "halloween", scare: str = "", tag: str = "",
         video: str = "", states_q: str = Query("", alias="states")):
    # states_q is the ?states=1 near-me opt-in; the alias keeps the
    # URL identical to the Auto Tour toggle's, and the distinct Python
    # name leaves the module-level states() helper callable below.
    cat = cat if cat in CATEGORIES else "halloween"
    # Feed-order rule (Dan, Oct 23): the default view is newest-first,
    # with Dan's hand-picked pins boosted to the very top. "Top" stays
    # available as an explicit sort choice only.
    sort = sort if sort in ("top", "new") else "new"
    # text search takes priority over dropdown
    town = town_search.strip() or town
    state = state.strip().upper()
    region = region.strip().lower()
    # Retention Wave 1, Item 1: visitor geo (Cloudflare headers) only ever
    # personalises the DEFAULT homepage. An explicit town/state/region in
    # the URL is an explicit choice and overrides geo completely; the
    # visitor's saved town (localStorage, rendered client-side by the
    # Near-you module's existing script) is likewise untouched.
    geo = None
    if not town and not state and not region:
        geo = _visitor_geo(request)
    order = "votes DESC, created_at DESC" if sort == "top" else "created_at DESC"
    query = "SELECT * FROM entries WHERE hidden = 0 AND category = ?"
    params: list = [cat]
    if town:
        # town may arrive as a dropdown label ('Atlantic Highlands, NJ'), a
        # bare city, or free text — match on the city, and on the state too
        # whenever one is known so NJ towns never leak into an MD view.
        city_part = extract_city(town)
        st_part = state or extract_state(town)
        variants = [city_part.lower()]
        for typo, fixed in CITY_FIXES.items():
            if fixed.lower() == city_part.lower() and typo not in variants:
                variants.append(typo)
        like = " OR ".join(["LOWER(town) LIKE ?"] * len(variants))
        query += f" AND ({like})"
        params.extend(f"%{v}%" for v in variants)
        if st_part:
            query += (" AND (LOWER(town) LIKE ? OR LOWER(town) LIKE ?"
                      " OR LOWER(town) LIKE ? OR LOWER(town) LIKE ?)")
            s = st_part.lower()
            params += [f"%, {s} %", f"%, {s}", f"%,{s} %", f"%,{s}"]
    elif region in ("boston", "dc-area"):
        terms = METRO_TERMS[region]
        placeholders = " OR ".join(["LOWER(town) LIKE ?"] * len(terms))
        query += f" AND ({placeholders})"
        params.extend([f"%{t}%" for t in terms])
    elif region in ("staten-island", "brooklyn", "manhattan", "queens", "bronx"):
        borough_terms = BOROUGH_TERMS[region]
        placeholders = " OR ".join(["LOWER(town) LIKE ?"] * len(borough_terms))
        query += f" AND ({placeholders})"
        params.extend([f"%{t}%" for t in borough_terms])
    elif region == "long-island":
        li_towns = LONG_ISLAND_TERMS
        placeholders = " OR ".join(["LOWER(town) LIKE ?"] * len(li_towns))
        query += f" AND ({placeholders})"
        params.extend([f"%{t}%" for t in li_towns])
    elif state:
        # match state as the trailing part: '%, NJ' or '%,NJ'
        query += " AND (LOWER(town) LIKE ? OR LOWER(town) LIKE ?)"
        params.append(f"%, {state.lower()}")
        params.append(f"%,{state.lower()}")
    if scare in ("family", "spooky", "creepy", "terrifying", "extreme"):
        query += " AND scare_level = ?"
        params.append(scare)
    if tag in ("animatronics", "inflatables", "handmade", "walkthrough", "projector", "lights", "music", "street-wide", "multi-house", "ticketed", "2025", "market", "oddities", "witchy", "craft", "flea", "free", "flagship", "21+"):
        query += " AND (',' || COALESCE(tags,'') || ',') LIKE ?"
        params.append(f"%,{tag},%")
    if video.strip() == "1":
        # "Has video": actual footage only — a TikTok embed/link or an
        # uploaded video file; photo-only pins drop out.
        query += (" AND ((tiktok_url IS NOT NULL AND TRIM(tiktok_url) != '')"
                  " OR LOWER(media_path) LIKE '%.mp4'"
                  " OR LOWER(media_path) LIKE '%.webm'"
                  " OR LOWER(media_path) LIKE '%.mov')")
    # Video-first ranking (engagement, Oct 22): pins with footage — a TikTok
    # URL or an uploaded video file, the same predicate as the "Has video"
    # filter above — sort ahead of photo-only pins; the chosen sort stays as
    # the stable secondary order within each group. Applies to the explicit
    # "Top" sort only: the default (newest) view follows Dan's Oct 23
    # feed-order rule — hand-picked pins first (newest hand-picked first),
    # then every other pin newest-first, with no video-first reshuffle.
    video_first = (
        "CASE WHEN ((tiktok_url IS NOT NULL AND TRIM(tiktok_url) != '')"
        " OR LOWER(media_path) LIKE '%.mp4'"
        " OR LOWER(media_path) LIKE '%.webm'"
        " OR LOWER(media_path) LIKE '%.mov') THEN 0 ELSE 1 END")
    if sort == "top":
        query += f" ORDER BY {video_first}, {order} LIMIT 100"
    else:
        query += " ORDER BY is_handpicked DESC, created_at DESC, id DESC LIMIT 100"
    with get_conn(DB_PATH) as conn:
        entries = [row_to_dict(r) for r in conn.execute(query, params).fetchall()]
        _attach_views(conn, entries)  # Item 7: feed cards show view counts
        sponsors = [dict(r) for r in conn.execute(
            "SELECT * FROM sponsors WHERE is_active = 1 ORDER BY "
            "CASE tier WHEN 'title' THEN 0 WHEN 'premium' THEN 1 ELSE 2 END, created_at").fetchall()]
        _tick_ph = ",".join("?" * len(TICKER_CATS))
        ticker_rows = conn.execute(
            "SELECT id, title, town, category, ev_type, lat, lng FROM entries "
            f"WHERE hidden = 0 AND category IN ({_tick_ph}) "
            "ORDER BY id DESC LIMIT 60", TICKER_CATS).fetchall()
    # Just-added ticker / update bar (Dan, Oct 23; announcement Dan,
    # Oct 25): the site's newest haunts + events, newest first, each
    # with a type emoji (markets = cart, events = ghost, the rest =
    # the pumpkin) and the derived 'City, ST' label used on every
    # card. The crawl LEADS with Dan's pinned announcement for the
    # Oct 25 national events batch (116 new events across every major
    # city), which carries its own href to /events instead of a pin
    # page.
    # Category rule (Dan, Oct 26): the ticker pool is haunts + events
    # ONLY (TICKER_CATS). After the Tour Fuel batch flooded the
    # recent-adds pool with restaurhaunts, shops and cafes, Dan
    # reserved the crawl for halloween displays, haunted houses and
    # events — venues, christmas, parks and live never appear. The
    # filter lives in the SQL above, so the LIMIT-60 window and every
    # ordering tier below operate on the eligible set alone: a visitor
    # whose nearest adds are all venues falls through to the state /
    # newest tiers instead of seeing venues or an empty bar.
    # Location-first ordering (Dan, Oct 25): "the new sites on the new
    # button should be relevant to the user's location and local
    # enough to visit." When the visitor's area is known (the same
    # Cloudflare-header geo the feed lead uses), the crawl leads with
    # adds near the visitor — within NEAR_RAIL_CAP_MI of their point,
    # or in their city — then adds from their state, then the newest
    # overall as filler, newest-first inside each bucket, so the bar
    # never empties. With no geo signal the crawl is simply the newest
    # 12 haunts + events, site-wide.
    if geo:
        vlat, vlng = geo.get("lat"), geo.get("lng")
        vstate = (geo.get("state") or "").upper()
        vcity = (geo.get("city") or "").strip().lower()

        def _ticker_bucket(r):
            if vlat is not None and vlng is not None \
                    and r["lat"] is not None and r["lng"] is not None \
                    and haversine_miles(vlat, vlng, r["lat"], r["lng"]) \
                    <= NEAR_RAIL_CAP_MI:
                return 0
            if vcity and extract_city(r["town"] or "").lower() == vcity \
                    and (not vstate
                         or extract_state(r["town"] or "") in ("", vstate)):
                return 0
            if vstate and extract_state(r["town"] or "") == vstate:
                return 1
            return 2

        ticker_rows = sorted(ticker_rows, key=_ticker_bucket)
    ticker_rows = ticker_rows[:12]
    ticker_items = []
    for r in ticker_rows:
        if r["ev_type"] == "Market":
            t_emoji = "\U0001F6D2"
        elif r["category"] == "events":
            t_emoji = "\U0001F47B"
        else:
            t_emoji = "\U0001F383"
        ticker_items.append({"id": r["id"], "emoji": t_emoji,
                             "title": (r["title"] or "").strip(),
                             "town": extract_city_state(r["town"] or "")})
    if ticker_items:
        ticker_items.insert(0, {"id": 0, "href": "/events", "announce": True,
                                "emoji": "\U0001F3AA",
                                "title": "NEW EVENTS posted in every city!",
                                "town": ""})
    # Item 1: resolve the visitor's area once — it drives both the
    # Near-you module (below) and the feed lead. With geo=None this is
    # exactly today's biggest-towns-site-wide behaviour.
    with get_conn(DB_PATH) as conn:
        halloween_inventory = _town_inventory(conn, "halloween")
    # State-loyal near-me (Dan, Oct 27): the Near-you resolution —
    # and with it the feed lead below — stays inside the visitor's own
    # state unless the module's "Include nearby states" toggle opted
    # into cross-state results (?states=1).
    near_multi = _states_opt_in(states_q)
    resolved_area = _resolve_visitor_area(halloween_inventory, geo,
                                          multi=near_multi)
    if geo and resolved_area["area_labels"]:
        # Lead the default feed with the visitor's area: area pins first
        # (in normal feed order), then the regular feed de-duped behind
        # them, still capped at 100 — the feed is re-led, never emptied.
        area_labels = resolved_area["area_labels"]
        if cat != "halloween":
            with get_conn(DB_PATH) as conn:
                cat_inventory = _town_inventory(conn, cat)
            area_labels = _resolve_visitor_area(
                cat_inventory, geo, multi=near_multi)["area_labels"]
        if area_labels:
            area_entries = _fetch_area_feed(cat, area_labels, scare, tag,
                                            video, sort)
            if area_entries:
                area_ids = {e["id"] for e in area_entries}
                entries = (area_entries +
                           [e for e in entries if e["id"] not in area_ids])[:100]
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    # Tonight's Display: fresh random pick on every homepage load from the
    # quality pool of real-media pins (Dan, Oct 22). The tonight_last
    # cookie carries the previous pick so a reload doesn't repeat it.
    # See _pick_tonights_display.
    try:
        from zoneinfo import ZoneInfo
        today_et = datetime.now(ZoneInfo("America/New_York")).date()
    except Exception:
        today_et = datetime.now(timezone.utc).date()
    last_raw = request.cookies.get("tonight_last", "")
    last_id = int(last_raw) if last_raw.isdigit() else None
    with get_conn(DB_PATH) as conn:
        tonight = _pick_tonights_display(conn, exclude_id=last_id)
        # Item 6: the Daily Fright band's display drop — deterministic
        # per ET date (same pool as Tonight's, different contract), so
        # the band names the same pin /daily leads with all day.
        daily = _daily_display(conn, today_et)
    daily_quiz = _trivia_quiz_for(datetime.now(timezone.utc).date())
    tonight_label = today_et.strftime("%A, %B ") + str(today_et.day)
    # First-screen modules (second-click #3): computed on EVERY homepage
    # view — all categories and filters — so the hero stack (laptop) and
    # the below-band copies (phone) stay consistent wherever the visitor
    # lands (Dan, Oct 22: "keep the blocks consistent"). The data is
    # discovery data and intentionally does NOT re-filter with the feed:
    # Near-you = the visitor's resolved area (Item 1; biggest haunt towns
    # overall when geo is unknown or an explicit location filter is in
    # the URL), Trending = top pins by detail-page views.
    with get_conn(DB_PATH) as conn:
        # Trending comes from the TTL-cached _trending() snapshot
        # (fortification pass 2) — it used to re-run the page_views
        # GROUP BY inline here on every homepage render.
        trending = _trending()
        # Near-you towns now come from the Item 1 resolution (geo-aware
        # when Cloudflare headers are present, biggest-site-wide when
        # not) computed above; the counts are the same live halloween
        # town counts this block used to compute inline.
        near_towns = resolved_area["chips"]
        # Top 10 by State hero block (Dan, Oct 23): the visitor's OWN
        # state's Top 10, personalized from the same _visitor_geo
        # signal Near You uses (geo["state"], Cloudflare region
        # headers). Unknown state — or a state with no pins in this
        # category — leaves home_top10 None and the template renders
        # the generic Top-10-by-state entry instead; a wrong state is
        # never presented as the visitor's.
        home_top10 = None
        visitor_state = (geo or {}).get("state") or ""
        if visitor_state:
            state_rows = [e for e in _entries_with_views(conn, cat)
                          if extract_state(e.get("town") or "")
                          == visitor_state]
            if state_rows:
                home_top10 = {
                    "code": visitor_state,
                    "name": US_STATE_NAMES.get(visitor_state,
                                               visitor_state),
                    "count": len(state_rows),
                    "entries": _rank_with_featured(state_rows, 10),
                }
    # Retention Wave 3, Item 5: the "Tonight" strip's anchor town.
    # Resolution: the visitor's explicit ?town= context first (their
    # chosen town, as-is). With a geo-resolved area (exact/near/state),
    # the anchor is the visitor's OWN town (the first Near-you chip) —
    # with two honest adjustments (Dan, Oct 23, LOCATION-FIRST: the
    # strip used to fall back to the biggest town on the map — Staten
    # Island — and show it to everyone): when the home town has no
    # events tonight, the anchor moves to the NEAREST town that does
    # have events tonight, named as that town and noted as such; when
    # no town nearby has events tonight either, the home town stays
    # and the events segment names its next event day instead of a
    # bare 0. A "nomap" visitor (area known, no mapped supply) anchors
    # on the nearest town with events tonight, else the biggest such
    # town in their state. A visitor with NO known location gets the
    # map-wide line (tonight's totals across the whole map) — no town
    # is ever presented as "near you" when it isn't. Displays =
    # halloween pins in the anchor town, from the same inventory that
    # builds the Near-you chips.
    strip_label, strip_note = "", ""
    strip_events_day = None
    strip_map_wide = False
    if town:
        want = extract_city_state(town) or town
        hit = next((t for t in halloween_inventory if t["label"] == want),
                   None)
        if hit is None:
            city_want = extract_city(town).lower()
            hit = next((t for t in halloween_inventory
                        if t["city"].lower() == city_want), None)
        strip_label = hit["label"] if hit else want
        strip_displays = hit["count"] if hit else 0
    elif resolved_area["mode"] in ("exact", "near", "state") \
            and resolved_area["chips"]:
        home_label = resolved_area["chips"][0]["label"]
        hit = next((t for t in halloween_inventory
                    if t["label"] == home_label), None)
        strip_label = home_label
        strip_displays = hit["count"] if hit else 0
        with get_conn(DB_PATH) as conn:
            tonight_counts = _events_on_by_town(conn, _today_et())
        if not tonight_counts.get(home_label):
            vpoint = None
            if geo and geo.get("lat") is not None \
                    and geo.get("lng") is not None:
                vpoint = (geo["lat"], geo["lng"])
            elif hit and hit["clat"] is not None:
                vpoint = (hit["clat"], hit["clng"])
            near_hit = (_nearest_events_town(tonight_counts,
                                             halloween_inventory, vpoint)
                        if vpoint else None)
            if near_hit:
                strip_label = near_hit["label"]
                strip_displays = near_hit["count"]
                strip_note = "nearest town with events tonight"
            else:
                with get_conn(DB_PATH) as conn:
                    nxt = _next_events_day(conn, home_label, _today_et())
                if nxt:
                    strip_events_day = nxt[0]
    elif resolved_area["mode"] == "nomap":
        with get_conn(DB_PATH) as conn:
            tonight_counts = _events_on_by_town(conn, _today_et())
        vpoint = None
        if geo and geo.get("lat") is not None \
                and geo.get("lng") is not None:
            vpoint = (geo["lat"], geo["lng"])
        near_hit = (_nearest_events_town(tonight_counts,
                                         halloween_inventory, vpoint)
                    if vpoint else None)
        if near_hit:
            strip_label = near_hit["label"]
            strip_displays = near_hit["count"]
            strip_note = "nearest town with events tonight"
        elif geo and geo.get("state"):
            in_state = [t for t in halloween_inventory
                        if t["state"] == geo["state"]
                        and tonight_counts.get(t["label"])]
            if in_state:
                best = max(in_state,
                           key=lambda t: (tonight_counts[t["label"]],
                                          t["count"], t["label"]))
                strip_label = best["label"]
                strip_displays = best["count"]
                strip_note = ("in " + US_STATE_NAMES.get(geo["state"],
                                                         geo["state"]))
            else:
                strip_map_wide = True
        else:
            strip_map_wide = True
    else:
        # Location entirely unknown (no geo headers): map-wide line.
        strip_map_wide = True
    if strip_map_wide:
        tstrip = _tonight_strip_map()
    elif strip_label:
        tstrip = _tonight_strip(strip_label, strip_displays, strip_note,
                                events_day=strip_events_day)
    else:
        tstrip = None
    # Welcome-back slimbar events segment (Dan, Oct 23): reuses the
    # Tonight strip's resolution wholesale — same anchor town, same
    # parsed-date count, same link target — compressed to one slim
    # link. Copy is deliberately terse ("9 tonight in Brooklyn, NY";
    # the strip further down carries the full "events on tonight"
    # wording): at 0.78rem the full phrasing measured ~226px and
    # pushed the phone bar past its two-line ceiling. "in {town}"
    # names where the events ARE, so it stays literally true in
    # every anchor mode (the visitor's own town, or the nearest town
    # with events tonight when theirs has none); a next-event-day
    # anchor names that day instead of "tonight". Map scope
    # (location unknown / no anchor) and a zero count fall back to
    # the plain discovery link — no invented town, no count.
    if tstrip and tstrip["scope"] == "town" and tstrip["events_on"]:
        _sn = tstrip["events_on"]
        if tstrip["events_iso"] == tstrip["today_iso"]:
            _stext = f"\U0001F3AA {_sn} tonight in {tstrip['town_label']}"
        else:
            _stext = (f"\U0001F3AA {_sn} in {tstrip['town_label']} "
                      f"{tstrip['events_when']}")
        slim_events = {
            "text": _stext,
            "href": ("/events?town="
                     + urllib.parse.quote(tstrip["town_label"])
                     + "&on=" + tstrip["events_iso"]),
        }
    else:
        slim_events = {"text": "\U0001F3AA Events near you \u2192",
                       "href": "/events"}
    response = templates.TemplateResponse(request, "index.html",
        {"request": request, "entries": entries, "sort": sort,
         "town": town, "towns": towns(cat, state), "states": states(cat),
         "state": state, "region": region, "voted": voted,
         "cat": cat, "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI,
         "scare": scare, "tag": tag, "video": "1" if video.strip() == "1" else "",
         "tonight": tonight, "tonight_label": tonight_label,
         "daily": daily, "daily_label": tonight_label,
         "daily_trivia_q": daily_quiz[0]["q"] if daily_quiz else "",
         "tstrip": tstrip,
         "slim_events": slim_events,
         "bracket_teaser": _bracket_teaser(),
         # Pop Haunt Culture homepage feature (Dan, Oct 27): the
         # section page's lead dict, shared so they can't drift.
         "pop_featured": POP_CULTURE_FEATURED,
         "trending": trending, "near_towns": near_towns,
         "home_top10": home_top10,
         "near_heading": resolved_area["heading"],
         "near_sub": resolved_area["sub"],
         "geo_mode": resolved_area["mode"],
         "geo_area": resolved_area["area_name"],
         # State-loyal near-me toggle state for the Near-you module
         # (mirrors the Auto Tour panel's scope row).
         "near_multi": near_multi,
         "near_state": resolved_area.get("state", ""),
         "near_state_name": US_STATE_NAMES.get(
             resolved_area.get("state", ""), resolved_area.get("state", "")),
         # Retention Wave 2, Item 1: town centroids for the homepage
         # one-tap locate prompt, in EXACTLY the row format detail
         # pages embed for the video chain ([label, city, state,
         # centroid lat, centroid lng, pin count]) and built from the
         # same _town_inventory halloween data — the browser picks the
         # nearest centroid to the visitor's geolocation fix and saves
         # that row's label as hm_town, the same value the Near-you
         # chips link to / the town flows store.
         "town_centers": [[t["label"], t["city"], t["state"],
                           t["clat"], t["clng"], t["count"]]
                          for t in halloween_inventory
                          if t["clat"] is not None
                          and t["clng"] is not None],
         "sponsors": sponsors,
         "ticker_items": ticker_items,
         "bottom_tabs": _place_tabs(cat, state, region, sort, scare, tag,
                                    "1" if video.strip() == "1" else ""),
         "tier_labels": {"featured": "Featured Sponsor", "premium": "Premium Sponsor", "title": "Title Sponsor"}},
    )
    if tonight:
        response.set_cookie("tonight_last", str(tonight["id"]),
                            max_age=7 * 24 * 3600, path="/", samesite="lax")
    return response


def _events_filter_data() -> dict:
    """The /events filter sidebar's data bundle: location maps (state /
    town counts + the raw town strings behind each derived label),
    region counts, facet counts and the total — all computed over
    EVERY visible event, independent of the current filter selection.
    TTL-cached + background-refreshed (fortification pass 2): building
    it ran four GROUP BY passes over the events category on every
    /events render. Callers get copies of every mutable member."""
    def build():
        state_counts: dict[str, int] = {}
        town_counts: dict[str, int] = {}
        town_state: dict[str, str] = {}
        raw_by_state: dict[str, list] = {}
        raw_by_town: dict[str, list] = {}
        town_groups: list = []
        with get_conn(DB_PATH) as conn:
            for r in conn.execute(
                    "SELECT town, COUNT(*) AS n FROM entries "
                    "WHERE hidden = 0 AND category = 'events' GROUP BY town").fetchall():
                raw = r["town"] or ""
                town_groups.append((raw, r["n"]))
                st = extract_state(raw)
                label = extract_city_state(raw)
                if st:
                    state_counts[st] = state_counts.get(st, 0) + r["n"]
                    raw_by_state.setdefault(st, []).append(raw)
                if label:
                    town_counts[label] = town_counts.get(label, 0) + r["n"]
                    raw_by_town.setdefault(label, []).append(raw)
                    if st:
                        town_state[label] = st
            counts: dict[str, dict[str, int]] = {}
            for key, col, _values, _labels in EVENT_FACETS:
                counts[key] = {r[col]: r["n"] for r in conn.execute(
                    f"SELECT {col}, COUNT(*) AS n FROM entries "
                    f"WHERE hidden = 0 AND category = 'events' AND {col} IS NOT NULL "
                    f"GROUP BY {col}").fetchall()}
            total = conn.execute(
                "SELECT COUNT(*) AS n FROM entries "
                "WHERE hidden = 0 AND category = 'events'").fetchone()["n"]
        region_counts = {
            slug: sum(n for raw, n in town_groups
                      if any(t in raw.lower()
                             for t in _region_terms(slug)))
            for slug, _label in REGION_TABS}
        return {"state_counts": state_counts, "town_counts": town_counts,
                "town_state": town_state, "raw_by_state": raw_by_state,
                "raw_by_town": raw_by_town, "town_groups": town_groups,
                "region_counts": region_counts, "counts": counts,
                "total": total}
    b = _ttl_cached("evfilter", build)
    return {"state_counts": dict(b["state_counts"]),
            "town_counts": dict(b["town_counts"]),
            "town_state": dict(b["town_state"]),
            "raw_by_state": {k: list(v) for k, v in b["raw_by_state"].items()},
            "raw_by_town": {k: list(v) for k, v in b["raw_by_town"].items()},
            "town_groups": list(b["town_groups"]),
            "region_counts": dict(b["region_counts"]),
            "counts": {k: dict(v) for k, v in b["counts"].items()},
            "total": b["total"]}


@app.get("/events", response_class=HTMLResponse)
def events_page(request: Request, type: str = "", genre: str = "",
                venue: str = "", sort: str = "top",
                state: str = "", town: str = "", region: str = "",
                on: str = "", near: str = "", area: str = "",
                lat: str = "", lng: str = ""):
    # The header's Events artwork links here (Dan, Oct 22). This used to
    # 302 to /?cat=events; it is now the canonical events page so events
    # can be searched by type / genre / venue style (Dan, Oct 22) with
    # shareable filtered URLs, e.g. /events?type=DJ+Party&genre=Jazz.
    # State + City dropdowns (Dan, Oct 22; laptop-only display, the params
    # work anywhere): event towns are free-text in the data (a clean
    # 'City, ST' or a full street address), so state/city are derived with
    # the same extract_state / extract_city_state helpers that build every
    # card's town_label. Filtering matches on the raw town strings behind
    # each derived value. Option counts are plain totals, exactly like the
    # facet counts above (not re-filtered by the other selections).
    sort = sort if sort in ("top", "new") else "top"
    selected = {"type": type if type in EVENT_TYPES else "",
                "genre": genre if genre in EVENT_GENRES else "",
                "venue": venue if venue in EVENT_VENUES else ""}
    # Region dropdown (Dan, Oct 23): the same curated REGION_TABS /
    # _region_terms definitions the homepage feed + place tabs use —
    # no second region semantics. An unknown slug is ignored (the page
    # behaves as today), exactly like an unparseable `on` below.
    region = region.strip().lower()
    region_labels = dict(REGION_TABS)
    if region not in region_labels:
        region = ""
    region_label = region_labels.get(region, "")
    region_terms = _region_terms(region) if region else []
    # Retention Wave 3, Item 5: ?on=YYYY-MM-DD date view. Events carry
    # dates only in their titles, so the filter is applied in Python via
    # parse_event_dates AFTER the facet/state/town SQL filters (it
    # composes with all of them) and BEFORE the 100-card cap, so a date
    # view never loses on-date events to the unfiltered cap. An
    # unparseable `on` value is ignored — the page behaves as today.
    on_date = None
    if on.strip():
        try:
            on_date = datetime.strptime(on.strip(), "%Y-%m-%d").date()
        except ValueError:
            on_date = None
    on_str = on_date.isoformat() if on_date else ""
    order = "votes DESC, created_at DESC" if sort == "top" else "created_at DESC"
    # Same video-first ranking as the home feed.
    video_first = (
        "CASE WHEN ((tiktok_url IS NOT NULL AND TRIM(tiktok_url) != '')"
        " OR LOWER(media_path) LIKE '%.mp4'"
        " OR LOWER(media_path) LIKE '%.webm'"
        " OR LOWER(media_path) LIKE '%.mov') THEN 0 ELSE 1 END")
    query = "SELECT * FROM entries WHERE hidden = 0 AND category = 'events'"
    params: list = []
    for key, col, _values, _labels in EVENT_FACETS:
        if selected[key]:
            query += f" AND {col} = ?"
            params.append(selected[key])
    # Filter sidebar data (location maps, region + facet counts,
    # total) from the TTL-cached bundle — see _events_filter_data.
    _fd = _events_filter_data()
    state_counts = _fd["state_counts"]
    town_counts = _fd["town_counts"]
    town_state = _fd["town_state"]
    raw_by_state = _fd["raw_by_state"]
    raw_by_town = _fd["raw_by_town"]
    town_groups = _fd["town_groups"]
    with get_conn(DB_PATH) as conn:
        state = state.strip().upper()
        if state not in state_counts:
            state = ""
        town = town.strip()
        if town not in town_counts:
            town = ""
        if state:
            raws = raw_by_state[state]
            query += f" AND town IN ({','.join('?' * len(raws))})"
            params += raws
        if town:
            raws = raw_by_town[town]
            query += f" AND town IN ({','.join('?' * len(raws))})"
            params += raws
        # Region counts over every visible event, in the curated
        # REGION_TABS order; matching is the place-tabs predicate — a
        # term appearing anywhere in the raw town string. Precomputed
        # in the cached filter bundle (fortification pass 2).
        region_counts = _fd["region_counts"]
        if region:
            raws = [raw for raw, _n in town_groups
                    if any(t in raw.lower() for t in region_terms)]
            if raws:
                query += f" AND town IN ({','.join('?' * len(raws))})"
                params += raws
            else:
                query += " AND 1 = 0"
        # "Events near me" (Dan, Oct 24 — STAGED for his preview): the
        # button at the top of /events lands here with ?near=1 plus one
        # of the location inputs the site already uses — ?lat=&lng=
        # from browser geolocation (the hmNearMe / /nearby flow),
        # ?area= carrying the visitor's saved town (localStorage
        # hm_town, the homepage's saved-town model) or a town picked
        # in the chooser below, or nothing at all, in which case the
        # Cloudflare headers the homepage Near You module reads
        # (_visitor_geo) get their chance. Resolution itself is the
        # homepage's own _resolve_visitor_area over the EVENTS town
        # inventory — exact town (+ neighbours within 75 mi), nearest
        # towns within 100 mi of the point, or the visitor's state —
        # never a second, invented proximity rule. The filter then
        # applies through the same raw-town map as the City dropdown,
        # so it composes with every facet/date filter and the by-day
        # grouping below exactly like a town pick does.
        near_active = False
        near_label = ""
        near_prompt = False
        near_nomap_name = ""
        if near:
            geo = None
            try:
                flat, flng = float(lat), float(lng)
                if -90 <= flat <= 90 and -180 <= flng <= 180:
                    geo = {"city": "", "state": "",
                           "lat": flat, "lng": flng}
            except (TypeError, ValueError):
                geo = None
            if geo is None and area.strip():
                acity = extract_city(area)
                if acity:
                    geo = {"city": acity,
                           "state": extract_state(area),
                           "lat": None, "lng": None}
            if geo is None:
                geo = _visitor_geo(request)
            resolved = (_resolve_visitor_area(
                _town_inventory(conn, "events"), geo) if geo else None)
            if resolved and resolved["mode"] in ("exact", "near", "state") \
                    and resolved["area_labels"]:
                raws = []
                for lbl in resolved["area_labels"]:
                    raws += raw_by_town.get(lbl, [])
                if raws:
                    query += f" AND town IN ({','.join('?' * len(raws))})"
                    params += raws
                    near_active = True
                    if resolved["mode"] == "state":
                        # Chips lead with the state's biggest town,
                        # which would mislabel the filter — name the
                        # state itself instead.
                        near_label = resolved["area_name"]
                    elif resolved["chips"]:
                        near_label = resolved["chips"][0]["label"]
                    else:
                        near_label = resolved["area_name"]
            if not near_active:
                # Asked for near but nothing resolved (no signal at
                # all, or a known area with zero mapped events): the
                # template opens the town chooser instead of silently
                # showing the whole country.
                near_prompt = True
                if resolved and resolved["mode"] == "nomap":
                    near_nomap_name = resolved["area_name"]
        # No SQL cap in any view (the events catalogue is ~553 rows):
        # the by-day grouping below runs over the full facet/state/
        # town/region-filtered set — a cap would silently cut whole
        # days off the end of the listing. The ?on= view still caps
        # its single day at 100 cards, as before.
        query += f" ORDER BY {video_first}, {order}"
        entries = [row_to_dict(r) for r in conn.execute(query, params).fetchall()]
        # Facet counts + total are filter-independent: from the cached
        # bundle (fortification pass 2).
        counts = _fd["counts"]
        total = _fd["total"]
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    facets = []
    for key, _col, values, labels in EVENT_FACETS:
        facets.append({
            "key": key, "selected": selected[key],
            "options": [{"value": v, "label": labels.get(v, v),
                         "count": counts[key][v]}
                        for v in values if counts[key].get(v)],
        })
    loc = {
        "state": state, "town": town,
        "region": region, "region_label": region_label,
        "region_options": [
            {"value": slug, "label": label, "count": region_counts[slug]}
            for slug, label in REGION_TABS if region_counts.get(slug)],
        "state_options": [
            {"value": code, "label": US_STATE_NAMES.get(code, code),
             "count": n}
            for code, n in sorted(state_counts.items(),
                                  key=lambda kv: (-kv[1], kv[0]))],
        "town_options": [
            {"value": label, "count": town_counts[label]}
            for label in sorted(town_counts)
            if not state or town_state.get(label) == state],
    }
    # Item 5 date view: keep only events whose parsed title span covers
    # the requested date (undated titles never match — documented in
    # parse_event_dates), then apply the usual 100-card cap.
    on_total = None
    if on_date is not None:
        entries = [e for e in entries if event_on_date(e["title"], on_date)]
        on_total = len(entries)
        entries = entries[:100]
    on_label = ""
    if on_date is not None:
        on_label = (on_date.strftime("%A, %B ") + str(on_date.day)
                    + on_date.strftime(", %Y"))
    # By-day organization (Dan, Oct 23): the listing is grouped under
    # per-day sections — America/New_York calendar days, soonest
    # first, never by week. A dated event appears once, under the
    # first day of its parsed run that is today or later (a run
    # already in progress sits under Tonight); a run that ended
    # before today has no section and drops off the listing. Titles
    # with no parseable date keep a trailing section so no live
    # listing is lost. In the ?on= view the filter above has already
    # reduced the set to the requested day, so it forms one section
    # headed by that day (the visitor lands on the day they asked
    # for); each section also carries a day-YYYY-MM-DD anchor.
    today = _today_et()
    day_groups = []
    if on_date is not None:
        if entries:
            day_groups.append({
                "label": _ev_day_label(on_date, today),
                "anchor": "day-" + on_date.isoformat(),
                "date": on_date,
                "entries": _ev_sort_day(entries, sort)})
    else:
        by_day: dict = {}
        undated: list = []
        for e in entries:
            span = parse_event_dates(e["title"])
            if span is None:
                undated.append(e)
            elif span[1] >= today:
                by_day.setdefault(max(span[0], today), []).append(e)
        for d in sorted(by_day):
            day_groups.append({
                "label": _ev_day_label(d, today),
                "anchor": "day-" + d.isoformat(),
                "date": d,
                "entries": _ev_sort_day(by_day[d], sort)})
        if undated:
            day_groups.append({
                "label": "More events — see the listing for dates",
                "anchor": "day-more",
                "date": None,
                "entries": _ev_sort_day(undated, sort)})
    entries = [e for g in day_groups for e in g["entries"]]
    # ---------------------------------------------------------------
    # Events upgrade (Dan, Oct 25 — from the time-on-page table:
    # /events pulled top-tier views at ~0s average active time; the
    # first screen was chrome, not an answer). Everything below
    # ANNOTATES the same listed set — day_groups / entries / counts
    # keep their exact semantics, so listing parity is structural:
    #   * per-entry _ev_day / _day_short / _start_label / _dist for
    #     the upgraded cards (date badge, start time, distance);
    #   * a SPOTLIGHT — the soonest day's best event: nearest to the
    #     visitor within the 50 mi visitable cap when a point
    #     resolves, else the day's biggest (votes, then video, then
    #     earliest start). Labelled Tonight only when it IS tonight;
    #   * a NEAR YOU lead — listed events within 50 mi of the
    #     visitor point, soonest first, ahead of (never instead of)
    #     the full day-grouped list;
    #   * chip data for the sticky client-side filter bar.
    # The visitor point: the explicit ?lat=&lng= fix when one rode
    # along, else _visitor_geo's Cloudflare coordinates, else the
    # centroid of the visitor's exact events town (the same cached
    # inventory the ?near= flow resolves against). No signal ->
    # _dist stays None and there is no near section; the page leads
    # with the day list exactly as before. Distances print only at
    # <= 50 mi — the standing "near means visitable" rule.
    ev_chrome = on_date is None
    _wd = today.weekday()
    _sat = today - timedelta(days=_wd - 5) if _wd >= 5 \
        else today + timedelta(days=5 - _wd)
    _weekend = {_sat, _sat + timedelta(days=1)}
    for g in day_groups:
        gd = g.get("date")
        g["rel"] = ("today" if gd == today else
                    "tomorrow" if gd == today + timedelta(days=1) else "")
        g["is_weekend"] = bool(gd and gd in _weekend)
    vpoint = None
    try:
        _flat, _flng = float(lat), float(lng)
        if -90 <= _flat <= 90 and -180 <= _flng <= 180:
            vpoint = (_flat, _flng)
    except (TypeError, ValueError):
        vpoint = None
    _geo = None
    if vpoint is None:
        _geo = _visitor_geo(request)
        if _geo and _geo.get("lat") is not None \
                and _geo.get("lng") is not None:
            vpoint = (_geo["lat"], _geo["lng"])
    if vpoint is None and _geo and (_geo.get("city") or _geo.get("state")):
        _cands = [t for t in _town_inventory(None, "events")
                  if _geo.get("city") and t["clat"] is not None
                  and t["city"].lower() == _geo["city"].lower()]
        if _geo.get("state"):
            _in_st = [t for t in _cands if t["state"] == _geo["state"]]
            if _in_st:
                _cands = _in_st
        if _cands:
            _t0 = sorted(_cands, key=lambda t: -t["count"])[0]
            vpoint = (_t0["clat"], _t0["clng"])

    def _fmt_start(mins):
        if mins is None:
            return None
        h24, m = divmod(mins, 60)
        return f"{h24 % 12 or 12}:{m:02d} {'AM' if h24 < 12 else 'PM'}"

    for g in day_groups:
        gd = g.get("date")
        for e in g["entries"]:
            e["_fff"] = _is_fall_family_fun(e)
            e["_ev_day"] = gd
            if gd is None:
                e["_day_short"] = ""
            elif gd == today:
                e["_day_short"] = "Tonight"
            elif gd == today + timedelta(days=1):
                e["_day_short"] = "Tomorrow"
            else:
                e["_day_short"] = gd.strftime("%a, %b ") + str(gd.day)
            e["_start_min"] = _event_start_minutes(e["title"])
            e["_start_label"] = _fmt_start(e["_start_min"])
            e["_dist"] = None
            if vpoint and e.get("lat") is not None \
                    and e.get("lng") is not None:
                e["_dist"] = round(haversine_miles(
                    vpoint[0], vpoint[1], e["lat"], e["lng"]), 1)
    spotlight = None
    near_events: list = []
    if ev_chrome:
        _dated = [g for g in day_groups if g.get("date")]
        if _dated:
            _pool = _dated[0]["entries"]
            _pick = None
            if vpoint:
                _near_pool = [e for e in _pool
                              if e["_dist"] is not None
                              and e["_dist"] <= 50]
                if _near_pool:
                    _pick = min(_near_pool, key=lambda e: (
                        e["_dist"], e["_start_min"] is None,
                        e["_start_min"] or 0, e["id"]))
            if _pick is None:
                def _big_key(e):
                    return (-(e["votes"] or 0),
                            0 if ((e.get("tiktok_url") or "").strip()
                                  or e.get("media_type") == "video")
                            else 1,
                            e["_start_min"] is None,
                            e["_start_min"] or 0, e["id"])
                _pick = min(_pool, key=_big_key)
            spotlight = {"entry": _pick, "date": _dated[0]["date"],
                         "is_tonight": _dated[0]["date"] == today,
                         "day_label": _ev_day_label(_dated[0]["date"],
                                                    today)}
        if vpoint:
            _cand = [e for g in _dated for e in g["entries"]
                     if e["_dist"] is not None and e["_dist"] <= 50]
            _cand.sort(key=lambda e: (
                e["_ev_day"], e["_start_min"] is None,
                e["_start_min"] or 0, e["_dist"], e["id"]))
            near_events = _cand[:8]
    _type_labels = {o["value"]: o["label"] for o in facets[0]["options"]}
    _type_counts: dict = {}
    for e in entries:
        if e.get("ev_type"):
            _type_counts[e["ev_type"]] = \
                _type_counts.get(e["ev_type"], 0) + 1
    chip_types = [{"value": v, "label": _type_labels.get(v, v), "count": n}
                  for v, n in sorted(_type_counts.items(),
                                     key=lambda kv: (-kv[1], kv[0]))]
    # Fall Family Fun (Dan, Oct 27): the computed-membership chip rides
    # the same bar, slotted by count like the type chips (the existing
    # chips keep their exact relative order).
    _fff_count = sum(1 for e in entries if e.get("_fff"))
    if _fff_count:
        _fff_pos = next((i for i, c in enumerate(chip_types)
                         if c["count"] < _fff_count), len(chip_types))
        chip_types.insert(_fff_pos, {
            "value": FALL_FAMILY_FUN_VALUE,
            "label": FALL_FAMILY_FUN_LABEL, "count": _fff_count})
    # Near-me state carried through the facet form + sort toggles as
    # hidden fields / a query fragment, so changing type/genre/sort
    # never drops the visitor's area. Bare "clear filters" links stay
    # the full reset (they are the Show-all-events path).
    near_fields = []
    if near:
        near_fields.append(("near", "1"))
        if area.strip():
            near_fields.append(("area", area.strip()))
        if lat.strip() and lng.strip():
            near_fields += [("lat", lat.strip()), ("lng", lng.strip())]
    near_qs = "&".join(
        f"{k}={urllib.parse.quote_plus(v)}" for k, v in near_fields)
    return templates.TemplateResponse(request, "events.html",
        {"request": request, "entries": entries, "sort": sort,
         "day_groups": day_groups,
         "spotlight": spotlight, "near_events": near_events,
         "chip_types": chip_types, "ev_chrome": ev_chrome,
         "facets": facets, "selected": selected, "total": total,
         "loc": loc,
         "filtered": any(selected.values()) or bool(state) or bool(town)
                     or bool(region) or bool(on_date) or near_active,
         "near_active": near_active, "near_label": near_label,
         "near_prompt": near_prompt, "near_nomap_name": near_nomap_name,
         "near_fields": near_fields, "near_qs": near_qs,
         "on": on_str, "on_label": on_label, "on_total": on_total,
         "voted": voted})


@app.get("/markets", response_class=HTMLResponse)
def markets_page(request: Request, town: str = "", state: str = "",
                 near: str = "", area: str = "", lat: str = "",
                 lng: str = ""):
    # Flea Markets & Pop-Ups (Dan, Oct 23): every event pin faceted
    # ev_type='Market' on one page, soonest first. Event dates live in
    # the titles, so ordering reuses parse_event_dates (the same parser
    # behind the /events ?on= view); undated titles sort last, by votes.
    # The set is small (dozens), so no cap is needed.
    # Location controls (Dan, Oct 24): a City/State dropdown of every
    # town that actually has markets (?town=, validated against the
    # derived 'City, ST' labels, the same extract_city_state labels the
    # cards show) plus a "Markets near me" button that mirrors Events
    # Near Me exactly — ?near=1 with ?area= (saved town / chooser pick),
    # ?lat=&lng= (browser geolocation) or bare (Cloudflare headers via
    # _visitor_geo), resolved by _resolve_visitor_area over the MARKETS
    # town inventory: exact town (+ neighbours within 75 mi), nearest
    # towns within 100 mi of the point, else the visitor's state, with
    # the town chooser as the fallback when nothing resolves.
    # State dropdown (Dan, Oct 27): a state select beside the town
    # dropdown (?state=, validated against the states the MARKET town
    # inventory actually covers, options counted and ordered like the
    # /events state dropdown). It filters the listing to one state,
    # narrows the town dropdown to that state's towns, and combines
    # with ?town= when both are given (both filters apply). "All
    # states" (empty value) is the clear path back.
    with get_conn(DB_PATH) as conn:
        entries = [row_to_dict(r) for r in conn.execute(
            "SELECT * FROM entries WHERE hidden = 0 AND category = 'events' "
            "AND ev_type = 'Market'").fetchall()]
        inventory = _town_inventory(conn, "events", "Market")
    total = len(entries)
    state_counts: dict[str, int] = {}
    for t in inventory:
        if t["state"]:
            state_counts[t["state"]] = (state_counts.get(t["state"], 0)
                                        + t["count"])
    state_options = [{"value": code,
                      "label": US_STATE_NAMES.get(code, code),
                      "count": n}
                     for code, n in sorted(state_counts.items(),
                                           key=lambda kv: (-kv[1], kv[0]))]
    state = state.strip().upper()
    if state not in state_counts:
        state = ""
    state_name = US_STATE_NAMES.get(state, state)
    town_options = [{"value": t["label"], "count": t["count"]}
                    for t in sorted(inventory, key=lambda t: t["label"])
                    if not state or t["state"] == state]
    town = town.strip()
    if town not in {t["label"] for t in inventory}:
        town = ""
    near_active = False
    near_label = ""
    near_prompt = False
    near_nomap_name = ""
    if near:
        geo = None
        try:
            flat, flng = float(lat), float(lng)
            if -90 <= flat <= 90 and -180 <= flng <= 180:
                geo = {"city": "", "state": "",
                       "lat": flat, "lng": flng}
        except (TypeError, ValueError):
            geo = None
        if geo is None and area.strip():
            acity = extract_city(area)
            if acity:
                geo = {"city": acity,
                       "state": extract_state(area),
                       "lat": None, "lng": None}
        if geo is None:
            geo = _visitor_geo(request)
        resolved = (_resolve_visitor_area(inventory, geo) if geo else None)
        if resolved and resolved["mode"] in ("exact", "near", "state") \
                and resolved["area_labels"]:
            keep = resolved["area_labels"]
            near_entries = [e for e in entries
                            if extract_city_state(e["town"] or "") in keep]
            if near_entries:
                entries = near_entries
                near_active = True
                if resolved["mode"] == "state":
                    near_label = resolved["area_name"]
                elif resolved["chips"]:
                    near_label = resolved["chips"][0]["label"]
                else:
                    near_label = resolved["area_name"]
        if not near_active:
            # Asked for near but nothing resolved (no signal at all, or
            # a known area with zero mapped markets): the template
            # opens the town chooser instead of silently showing the
            # whole country.
            near_prompt = True
            if resolved and resolved["mode"] == "nomap":
                near_nomap_name = resolved["area_name"]
    elif state or town:
        if state:
            entries = [e for e in entries
                       if extract_state(e["town"] or "") == state]
        if town:
            entries = [e for e in entries
                       if extract_city_state(e["town"] or "") == town]

    def _soonest(e):
        span = parse_event_dates(e["title"])
        if span:
            return (0, span[0].toordinal(), -(e["votes"] or 0), e["id"])
        return (1, 0, -(e["votes"] or 0), e["id"])

    entries.sort(key=_soonest)
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    return templates.TemplateResponse(request, "markets.html",
        {"request": request, "entries": entries, "total": total,
         "town_options": town_options, "town": town,
         "state": state, "state_name": state_name,
         "state_options": state_options,
         "near_active": near_active, "near_label": near_label,
         "near_prompt": near_prompt, "near_nomap_name": near_nomap_name,
         "voted": voted})


RESTAURHAUNT_CATS = ("restaurants", "coffee", "shops")


@app.get("/restaurhaunts", response_class=HTMLResponse)
def restaurhaunts(request: Request, sort: str = "new", f: str = "all",
                  town_search: str = ""):
    # Combined "Restaurhaunts & Cafes" listing (Dan, Oct 22): one mixed
    # feed over the existing restaurants + coffee + shops categories
    # (bars live in restaurants). Category keys are unchanged — only the
    # display word became "restaurhaunts". Each card carries its own
    # category chip so the mix stays legible.
    # Feed-order rule (Dan, Oct 23): default sort is newest (hand-picked
    # first, then newest-first); "Top" is an explicit choice only.
    # Restaurhaunts ordering (Dan, Oct 26): the DEFAULT view of this
    # venue lane leads with the most decked-for-Halloween places
    # (decked_score), then the Oct 23 chain (hand-picked, newest)
    # breaks ties. "Top" keeps its votes order untouched.
    sort = sort if sort in ("top", "new") else "new"
    f = f if f in ("all",) + RESTAURHAUNT_CATS else "all"
    query = ("SELECT * FROM entries WHERE hidden = 0 "
             "AND category IN ('restaurants', 'coffee', 'shops')")
    params: list = []
    if f != "all":
        query += " AND category = ?"
        params.append(f)
    town_search = town_search.strip()
    if town_search:
        query += " AND LOWER(town) LIKE ?"
        params.append(f"%{extract_city(town_search).lower()}%")
    if sort == "top":
        query += " ORDER BY votes DESC, created_at DESC LIMIT 100"
    with get_conn(DB_PATH) as conn:
        entries = [row_to_dict(r) for r in conn.execute(query, params).fetchall()]
    if sort != "top":
        # Stable sorts in reverse priority order (the /nearby pattern):
        # the last sort applied is the primary key.
        entries.sort(key=lambda e: e["id"], reverse=True)
        entries.sort(key=lambda e: e.get("created_at") or "", reverse=True)
        entries.sort(key=lambda e: 0 if e.get("is_handpicked") else 1)
        entries.sort(key=lambda e: -decked_score(e))
        entries = entries[:100]
    # Category tab counts from the shared TTL cache (fortification
    # pass 2) instead of a per-render GROUP BY over entries.
    all_counts = _category_counts()
    counts = {c: all_counts.get(c, 0) for c in RESTAURHAUNT_CATS}
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    return templates.TemplateResponse(request, "restaurhaunts.html",
        {"request": request, "entries": entries, "sort": sort, "f": f,
         "town_search": town_search, "counts": counts, "voted": voted,
         "total": sum(counts.values()),
         "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI})


@app.get("/upload", response_class=HTMLResponse)
def upload_form(request: Request):
    return templates.TemplateResponse(request, "upload.html", {"request": request, "error": None, "values": {}})


@app.get("/nearby", response_class=HTMLResponse)
def nearby(request: Request, q: str = "", miles: float = 10, cat: str = "halloween",
           sort: str = "new", lat: str = "", lng: str = "", states: str = ""):
    cat = cat if cat in CATEGORIES else "halloween"
    # Default sort is newest per Dan's Oct 23 feed-order rule (it is the
    # within-distance tiebreak here; distance always stays primary).
    sort = sort if sort in ("top", "new") else "new"
    # State-loyal default (Dan, Oct 27): results stay inside the
    # search center's state unless the visitor opts into nearby
    # states with the page's toggle (?states=1) — the same rule and
    # the same toggle as the Auto Tour panel.
    multi = _states_opt_in(states)
    try:
        miles = max(1, min(float(miles), 500))
    except (TypeError, ValueError):
        miles = 10
    entries: list = []
    err: str | None = None
    center: tuple[float, float] | None = None
    # direct coordinates (from "Near me" geolocation) take priority over text query
    if lat.strip() and lng.strip():
        try:
            center = (float(lat), float(lng))
            q = "your location"
        except ValueError:
            err = "Invalid location coordinates."
    if center is None and q.strip() and q != "your location":
        center = geocode_nominatim(q.strip())
        if center is None:
            err = f"Couldn't find '{q.strip()}'. Try a town or city name."
    if center is not None:
        # Rows from the shared _category_rows snapshot (fortification
        # pass 2) instead of a per-render scan + row_to_dict pass; the
        # distance annotation lands on the per-request copies.
        clat, clng = center
        for d in _category_rows(cat):
            if d["lat"] is None or d["lng"] is None:
                continue
            d["distance"] = haversine_miles(clat, clng, d["lat"], d["lng"])
            if d["distance"] <= miles:
                entries.append(d)
        # Sort by distance first, then the chosen order as tiebreak
        # (stable sorts, applied in reverse priority order). Newest —
        # the default — means hand-picked first, then newest-first,
        # matching the site's feed-order rule (Dan, Oct 23).
        entries.sort(key=lambda e: e.get("created_at") or "", reverse=True)
        if sort == "top":
            entries.sort(key=lambda e: -(e.get("votes") or 0))
        else:
            entries.sort(key=lambda e: 0 if e.get("is_handpicked") else 1)
        entries.sort(key=lambda e: e["distance"])
        if cat in RESTAURHAUNT_CATS:
            # Restaurhaunts ordering (Dan, Oct 26): the radius still
            # scopes the set, but inside it the most decked-for-
            # Halloween venues lead; the chain above (distance, then
            # the chosen sort) breaks ties (stable sort).
            entries.sort(key=lambda e: -decked_score(e))
    # State-loyal filter: the center's state, cheapest source first —
    # a state the query itself names ("Hackensack, NJ"), then the
    # visitor-geo state when this center IS the visitor (a Near-me
    # fix near the CF point), then a reverse lookup on the center.
    # No state from any source = radius-only, exactly as before.
    center_state = ""
    wide_count = len(entries)
    if center is not None:
        if q and q != "your location":
            center_state = _state_from_place_query(q)
        if not center_state:
            geo = _visitor_geo(request)
            if geo and geo.get("state") and geo.get("lat") is not None \
                    and geo.get("lng") is not None and haversine_miles(
                        center[0], center[1], geo["lat"], geo["lng"]) <= 25.0:
                center_state = geo["state"]
        if not center_state:
            center_state = _state_code_for_point(center[0], center[1])
        if center_state and not multi:
            entries = [e for e in entries
                       if extract_state(e.get("town") or "")
                       == center_state]
    center_params: dict[str, str] = {}
    if q and q != "your location":
        center_params = {"q": q}
    elif center is not None:
        center_params = {"lat": str(center[0]), "lng": str(center[1])}
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    return templates.TemplateResponse(request, "nearby.html",
        {"request": request, "entries": entries, "q": q, "miles": miles,
         "err": err, "voted": voted, "cat": cat, "cat_labels": CAT_LABELS,
         "cat_emoji": CAT_EMOJI, "sort": sort,
         # Town dropdown options for the search field — the same
         # 'City, ST' labels the homepage town filter offers.
         "town_options": towns(cat),
         # State-loyal scope row (mirrors the Auto Tour panel).
         "multi": multi, "center_state": center_state,
         "center_state_name": US_STATE_NAMES.get(center_state,
                                                 center_state),
         "wide_count": wide_count, "center_params": center_params},
    )


@app.get("/map", response_class=HTMLResponse)
def map_view(request: Request, cat: str = "halloween"):
    """Full-screen map with all haunt pins, Google Maps-style browsing."""
    cat = cat if cat in CATEGORIES else "halloween"
    # Rows from the shared _category_rows snapshot (fortification
    # pass 2) instead of a per-render scan + row_to_dict pass.
    pins = [e for e in _category_rows(cat)
            if e["lat"] is not None and e["lng"] is not None]
    return templates.TemplateResponse(request, "map.html",
        {"request": request, "pins": pins, "cat": cat,
         "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI},
    )


DIY_VIDEOS = [
    {"title": "DIY Concrete Pumpkins — Cast Once, Keep Them Forever", "creator": "@organizedandsimplified4u", "url": "https://www.tiktok.com/@organizedandsimplified4u/video/7689115065081023774", "video_id": "7689115065081023774", "blurb": "Stop buying pumpkins that rot: she pours wet concrete into a plastic jack-o'-lantern pail, lets it set, and demolds a grinning pumpkin built to last season after season. Her best trick comes after Halloween — turn the face to the wall and the same pumpkin moonlights as a flower pot."},
    {"title": "Custom Chucky Air Jordan 1s — Hand-Painted Sneaker DIY", "creator": "@thekickfix", "url": "https://www.tiktok.com/@thekickfix/video/7695269928751992095", "video_id": "7695269928751992095", "blurb": "The Kick Fix turns a plain pair of Air Jordan 1 Retro Highs into Chucky himself: denim-blue overall panels and the Good Guys striped-shirt colors hand-painted on, a flesh-tone toe box scarred with real hand-stitched thread, and bright orange laces to finish the killer-doll look. A wearable Child's Play tribute, built entirely by hand."},
    {"title": "Circus Ticket Booth DIY — Cardboard Carnival Build", "creator": "@arielviewtravelvlog", "url": "https://www.tiktok.com/@arielviewtravelvlog/video/7682846593799703821", "video_id": "7682846593799703821", "blurb": "Erica turns a plain cardboard cabinet box into a full circus ticket booth — gold TICKETS marquee, red velvet curtains, a grinning clown manning the window, and printed 'come one, come all' tickets fanned out on the counter. She admits she got so into the project she forgot to film half of it — the finished booth speaks for itself."},
    {"title": "Creepy Cotton Candy — Freak Show Concession Stand DIY", "creator": "@itgirlchay", "url": "https://www.tiktok.com/@itgirlchay/video/7695462926676659470", "video_id": "7695462926676659470", "blurb": "Part 4 of her porch-to-freak-show transformation: concession stand item #3 is a giant fake cotton candy — a pink spun-sugar puff on a cone, crawling with plastic spiders. It joins her fake popcorn buckets (rat garnish included) in the creepiest carnival snack lineup on the block."},
    {"title": "One Kid, Three Trick-or-Treaters — Mannequin Illusion Costume DIY", "creator": "@justinflom", "url": "https://www.tiktok.com/@justinflom/video/7693946321501179166", "video_id": "7693946321501179166", "blurb": "Justin Flom builds his daughter a wearable rig carrying two mannequin 'friends' — Ghostface on one side, a sheet ghost on the other — so one kid in a blue wig and yellow raincoat shows up looking like three trick-or-treaters, each holding its own pumpkin bucket. When she turns around and shows the costume, the illusion lands."},
    {"title": "Fun House Sign DIY — CarnEVIL Carnival Tutorial", "creator": "@bananabread_94", "url": "https://www.tiktok.com/@bananabread_94/video/7701188355186330911", "video_id": "7701188355186330911", "blurb": "A step-by-step build of a carnival Fun House sign — she says the letters were the hardest part of the whole project, but they definitely paid off. Prime entrance signage for a carnEVIL-themed setup."},
    {"title": "Michael Myers Cleaver Serving Board DIY", "creator": "@bowerbirdworkshop", "url": "https://www.tiktok.com/@bowerbirdworkshop/video/7701472320233164063", "video_id": "7701472320233164063", "blurb": "Followers asked for it, so they built it — a handmade serving board shaped like a butcher's cleaver, with Michael Myers' mask set into the black resin river down the middle, blood drip and all. A little horror for the serving table."},
    {"title": "Monster-in-a-Box Optical Illusion Costume DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7700739541933493517", "video_id": "7700739541933493517", "blurb": "It looks like she's holding a terrifying monster that's literally bursting out of a box — but it's all an optical illusion, built from scratch. She pieces together the structure and materials, then walks through how every detail sells the trick."},
    {"title": "5-Foot Chucky Doll Box DIY", "creator": "@darkhousedesigns", "url": "https://www.tiktok.com/@darkhousedesigns/video/7695179364945644831", "video_id": "7695179364945644831", "blurb": "Build a life-size Good Guys toy box for a Home Depot Chucky doll — 5 x 3 x 2 feet, framed with 2x2s and half-inch foam, finished with printed banners for the full Child's Play look."},
    {"title": "DIY Circus Tent — Halloween Party Build", "creator": "Taylor Booth (@theballoonchickaz)", "url": "https://www.tiktok.com/@theballoonchickaz/video/7698864214865087775", "video_id": "7698864214865087775", "blurb": "A full-size circus tent, built from scratch for a Halloween party — Taylor's whole process in 85 seconds. 229K views and counting, and you'll see why."},
    {"title": "Fog Chiller DIY — Maiden Voyage", "creator": "@theblackirishouse", "url": "https://www.tiktok.com/@theblackirishouse/video/7693254709972372767", "video_id": "7693254709972372767", "blurb": "Chill your fog machine's output and the fog hugs the ground like a graveyard at dawn. This build's first run shows exactly how it's done."},
    {"title": "Fog Chiller v2.0 — The Upgrades", "creator": "@theblackirishouse", "url": "https://www.tiktok.com/@theblackirishouse/video/7694109884777893150", "video_id": "7694109884777893150", "blurb": "Version two of the chiller: a legit spider web and frozen water bottles join the build for thicker, lower fog."},
    {"title": "Low-Lying Fog Setup — Full Rundown", "creator": "@theblackirishouse", "url": "https://www.tiktok.com/@theblackirishouse/video/7696612187141360926", "video_id": "7696612187141360926", "blurb": "Everyone asked, so here's the quick rundown of the whole low-lying fog setup — how the chiller is plumbed and why it works."},
    {"title": "Fog Chiller at Full Send", "creator": "@theblackirishouse", "url": "https://www.tiktok.com/@theblackirishouse/video/7699253873872997662", "video_id": "7699253873872997662", "blurb": "Less than a minute of ideal conditions — and the chiller was RIPPIN'. The maiden-voyage build, proven in the wild."},
    {"title": "The Junk-Drawer Glow Trick", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7700009652347587854", "video_id": "7700009652347587854", "blurb": "One simple trick hiding in your junk drawer turns ordinary specimen jars into glowing, radioactive-looking decor. You already own everything you need."},
    {"title": "Radioactive Specimen Jar DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7699612887765028109", "video_id": "7699612887765028109", "blurb": "This spooky specimen jar looks like it's glowing from the inside — the radioactive lab piece your mad-scientist corner was missing."},
    {"title": "Jar of Moving Eyeballs DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7698888739572976910", "video_id": "7698888739572976910", "blurb": "She made a jar of eyeballs that MOVE. Creepy, clever, and impossible to stop watching."},
    {"title": "Pirate Skeleton DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7698131249034005774", "video_id": "7698131249034005774", "blurb": "Another Halloween DIY — and it might be her favorite yet. Pirate bones done right."},
    {"title": "Witch's Cauldron DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7698064196147236109", "video_id": "7698064196147236109", "blurb": "Every witch needs a cauldron — and this one may have gotten a little carried away."},
    {"title": "Best Halloween DIYs in 20 Seconds", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7698024441569234190", "video_id": "7698024441569234190", "blurb": "Months of crafting, creativity and chaos in one rapid-fire highlight reel."},
    {"title": "Boo-zy Bones Drinking Skeletons", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7697775692141890829", "video_id": "7697775692141890829", "blurb": "These skeletons have been drinking for centuries…"},
    {"title": "Peeing Skeleton Dog DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7697651205543169294", "video_id": "7697651205543169294", "blurb": "Even in the afterlife, dogs still gotta go."},
    {"title": "Haunted Dollhouse DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7697030306649492749", "video_id": "7697030306649492749", "blurb": "Who knew a 1991 Playskool dollhouse could turn into something so creepy?"},
    {"title": "The Boo-zy Skeleton Fountain", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7696649206160837902", "video_id": "7696649206160837902", "blurb": "A skeleton chilling in a bubbling green fountain — the porch centerpiece your neighbors will copy next year."},
    {"title": "Slimed House DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7693296146705403149", "video_id": "7693296146705403149", "blurb": "She slimed her whole house for Halloween — gutters and all — and it turned out amazing."},
    {"title": "I Slimed My House — The Full Build", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7692867820584996110", "video_id": "7692867820584996110", "blurb": "The full start-to-finish build behind the slime house: expanding foam sprayed over pool noodles, painted radioactive neon green, then hung all along the gutters so the house looks like it's oozing goo. By night the drips glow under the Halloween lights."},
    {"title": "Pendant-Light Skeleton Club", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7694066781580758285", "video_id": "7694066781580758285", "blurb": "She posed mini skeletons on her kitchen pendant lights — heels and all — and 3 million viewers agree it's the hottest Halloween club in town. Proof decor doesn't have to be scary."},
    {"title": "Easiest Halloween DIY of the Year", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7690324637577710862", "video_id": "7690324637577710862", "blurb": "Quite possibly the easiest Halloween DIY she's made all year."},
    {"title": "Disgusting Dollar Tree Eyeballs", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7689903755977837837", "video_id": "7689903755977837837", "blurb": "Dollar Tree eyeballs… but make them DISGUSTING."},
    {"title": "Spooky Sparkly Eyeball DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7687246122758278413", "video_id": "7687246122758278413", "blurb": "Spooky, sparkly, and just the right amount of creepy."},
    {"title": "Pumpkin Wine Server DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7687019977131543821", "video_id": "7687019977131543821", "blurb": "Why serve wine from a boring bottle when you can serve it from a pumpkin?"},
    {"title": "Real Pumpkin Drink Dispenser", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7686647862247132429", "video_id": "7686647862247132429", "blurb": "A REAL pumpkin turned into a drink dispenser — a favorite fall DIY."},
    {"title": "Creepy Specimen Jar DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7684805348368141581", "video_id": "7684805348368141581", "blurb": "The creepiest little specimen jar — a preserved hand in a jar."},
    {"title": "Floating Eyeball DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7684008356431908110", "video_id": "7684008356431908110", "blurb": "This floating eyeball DIY is WAY easier than it looks."},
    {"title": "Garden Fence Glow-Up", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7683645655490841869", "video_id": "7683645655490841869", "blurb": "Wait until you see what she turned a cheap plastic garden fence into."},
    {"title": "Simplest DIY Ever", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7683271607695002893", "video_id": "7683271607695002893", "blurb": "Quite possibly the simplest DIY she's ever done — starting from a found plate."},
    {"title": "$3 DIY That Looks Expensive", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7683255523625487629", "video_id": "7683255523625487629", "blurb": "A stylish $3 DIY that looks WAY more expensive than it is."},
    {"title": "Preserved Specimen DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7682907699306155278", "video_id": "7682907699306155278", "blurb": "Her favorite creepy DIY yet — a preserved specimen straight out of a mad lab."},
    {"title": "Looks Complicated, Isn't DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7682859305539734797", "video_id": "7682859305539734797", "blurb": "This Halloween DIY looks WAY more complicated than it actually is."},
    {"title": "Glowing Gate Tutorial", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7560463323624443150", "video_id": "7560463323624443150", "blurb": "A HUGE 10-foot gate that glows — a true statement piece for your haunt entrance, and the full tutorial walks the whole build."},
]

DIY_VIDEOS_NICK = [
    {"title": "Who's Hungry!? — One-Hour DIY", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7699008843090595085", "video_id": "7699008843090595085", "blurb": "A fun, easy DIY that took less than an hour to build — fresh off the Nightmare Factory workbench."},
    {"title": "Gravestone Crawler DIY Tutorial", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7684419946595552526", "video_id": "7684419946595552526", "blurb": "Their first full tutorial — a fun, easy Gravestone Crawler you can build along with, step by step."},
    {"title": "Meet the Gravestone Crawler", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7684153715183439118", "video_id": "7684153715183439118", "blurb": "The Gravestone Creeper got a friend — meet the Crawler, the prop reveal that kicked off the tutorials."},
    {"title": "Gravestone Creeper DIY Tutorial", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7685645350278860046", "video_id": "7685645350278860046", "blurb": "Tutorial number two: create your very own Gravestone Creeper."},
    {"title": "DIY Gravestone Creeper — Home Depot Upgrade", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7680823981682789646", "video_id": "7680823981682789646", "blurb": "A quick and easy prop upgrade — a DIY Gravestone Creeper built from Home Depot's 2026 Halloween decor."},
    {"title": "Tree Thrashing Maniac DIY Tutorial", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7696416899118140686", "video_id": "7696416899118140686", "blurb": "You asked for it — the Tree Thrashing Maniac build, straight from the Nightmare Factory."},
    {"title": "Budget-Friendly DIY Build", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7688189975849946381", "video_id": "7688189975849946381", "blurb": "A fun, budget-friendly build from just a few hardware-store and dollar-store items — an easy home-haunt upgrade."},
    {"title": "Melting-Flesh Skeleton Wrap", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7685274761705852173", "video_id": "7685274761705852173", "blurb": "Stretch film plus a heat gun equals melting flesh — a genius glow-up for that old skeleton in the garage."},
    {"title": "Haunted Circus Room Transformation", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7696984421970365709", "video_id": "7696984421970365709", "blurb": "One room at a time toward a haunted circus Halloween party — a cheap, easy DIY transformation."},
    {"title": "Make a Store-Bought Skeleton Your Own", "creator": "@nicksnightmarefac", "url": "https://www.tiktok.com/@nicksnightmarefac/video/7682201723997277454", "video_id": "7682201723997277454", "blurb": "Endless ways to bring a basic store-bought skeleton to life and make it unmistakably yours."},
]


DIY_VIDEOS_BROOKLYN = [
    {"title": "Spinning Jack-o'-Lantern", "creator": "@heybrooklynb", "url": "https://www.tiktok.com/@heybrooklynb/video/7696976404730137887", "video_id": "7696976404730137887", "blurb": "She made her jack-o'-lantern SPIN — the carved-pumpkin hack your porch needs this year."},
    {"title": "Skeleton Tombstone Pop-Up Craft", "creator": "@heybrooklynb", "url": "https://www.tiktok.com/@heybrooklynb/video/7692588485563239711", "video_id": "7692588485563239711", "blurb": "A DIY skeleton craft that pops out of its tombstone — wait until you see it lit up at night."},
    {"title": "Glow-in-the-Dark Sorting Hat", "creator": "@heybrooklynb", "url": "https://www.tiktok.com/@heybrooklynb/video/7694068054950546719", "video_id": "7694068054950546719", "blurb": "A handmade Sorting Hat that glows in the dark — part prop, part costume, all magic."},
]


@app.get("/diy", response_class=HTMLResponse)
def diy_page(request: Request):
    return templates.TemplateResponse(
        request, "diy.html",
        {"videos": DIY_VIDEOS, "nick_videos": DIY_VIDEOS_NICK,
         "brooklyn_videos": DIY_VIDEOS_BROOKLYN},
    )


# ------------------------------------------------------------- diy costumes
# Curated costume ideas (Dan, Oct 22): OUR OWN short write-ups only — the full
# step-by-step instructions live at each credited source, linked from every
# card. PHOTOS ARE NEVER OURS AND NEVER COPIED (Dan, Oct 22 rework): every
# card shows the creator's own photo or video through the platform's official
# embed — a Pinterest pin embed ("pin" = pin id), a YouTube click-to-play
# facade ("yt" = video id) or a TikTok embed ("tt" = video id) — served by
# the platform with the creator's credit
# and link-back. Tutorials with no embeddable post of the costume are NOT
# shown; they sit on the permission-ask list
# (files/diy-costumes-permission-asks.md) until the creator says yes.

COSTUME_SECTIONS = [
    {
        "id": "just-added",
        "title": "&#x2B50; Just Added",
        "sub": "The newest costumes on the page — fresh from the feed, straight to the top.",
        "ideas": [
            {"name": "Zipper Face SFX Makeup — the Cute-Meets-Gore Unzip", "who": "Adults & teens", "difficulty": "Medium", "time": "About 1–2 hours",
             "materials": "Scar wax, a real zipper, fake blood and chunky gore for the exposed flesh, glam eye makeup, a long wig and bows for the cutesy finish",
             "blurb": "SCL Beauty glues a real zipper straight down the center of her face, seals the edges in scar wax, then unzips the lower half and packs the opening with raw, textured gore — fake blood and chunky 'exposed flesh' running from nose to neck. Then the twist her caption promises — 'a cutesy Halloween tutorial': full glam on the skin that's left, a black pigtail wig and white bows on top. Adorable from across the room, horrifying up close. Her honest review: 'I need practice with scar wax' — so give yourself a trial run before Halloween night. Tap the video and watch the face unzip.",
             "source": "@sclbeauty", "url": "https://www.tiktok.com/@sclbeauty/video/7693066020348513558", "tt": "7693066020348513558"},
            {"name": "Michael Myers × Jason Mashup Mask — Half-and-Half Slasher Build", "who": "Adults & teens", "difficulty": "Medium", "time": "An afternoon",
             "materials": "A Michael Myers mask, a Jason-style hockey mask, painter's tape, a craft knife, paint for the weathered finish — the video shows every cut and join",
             "blurb": "What if Michael Myers was Jason? This build answers it with a craft knife: a Myers mask and a hockey mask, each cut down and fused into a single half-and-half face — Haddonfield on one side, Camp Crystal Lake on the other — then taped off and weathered until the seam looks like it was always there. Tap the video and watch the two slashers become one mask.",
             "source": "@lydia_mary_ivy", "url": "https://www.tiktok.com/@lydia_mary_ivy/video/7686704472973708558", "tt": "7686704472973708558"},
            {"name": "Silent Hill Nurse Mask — Freestyle Bandage Build", "who": "Adults & teens", "difficulty": "Medium", "time": "An afternoon",
             "materials": "Gauze bandage wrap over a head form or mask base, a plain nurse cap you can mark with the red cross, dark red paint or fake blood for the weathering",
             "blurb": "Ekaterina freestyled the Dark Nurse her own way: a head wrapped in layer after layer of bandage gauze, stained and darkened until it turns fleshy and wrong, then crowned with the blood-flecked nurse cap and its red cross. No pattern and no plan — her whole caption is 'It was a lot of freestyle, but I love the way it came out,' and the finished mask backs her up. Tap the video and watch the wrap come together.",
             "source": "@eka_herself", "url": "https://www.tiktok.com/@eka_herself/video/7698457826687044886", "tt": "7698457826687044886"},
            {"name": "Carried Away in a Trash Can — Skeleton Garbage Man Illusion Costume", "who": "Adults & teens", "difficulty": "Medium", "time": "An afternoon",
             "materials": "A poseable skeleton, hi-vis safety jacket, cap and sunglasses, work gloves, jeans and boots, a wheeled trash can you can cut head and arm holes in",
             "blurb": "The garbage man is a skeleton: a poseable skeleton in a hi-vis jacket, cap and sunglasses gets mounted at the wearer's waist, its gloved hands gripping a wheeled trash can with holes cut in the side. The wearer pops his own head and arm out of the can while his legs do the walking — so a skeleton trash collector appears to be hauling him away, very much against his will. Filed by its creator under last-minute costumes, and the build really is one afternoon. Tap the video and watch the rig come together.",
             "source": "@deedomo12", "url": "https://www.tiktok.com/@deedomo12/video/7691812628582255902", "tt": "7691812628582255902"},
            {"name": "Easy SFX Wound Makeup — Fake-Blood Cheek Gashes", "who": "Adults & teens", "difficulty": "Easy", "time": "Under 30 minutes",
             "materials": "A flesh-toned wound piece (scar wax or a stick-on appliance) for each cheek, foundation to blend the edges, dark shadow for depth, fake blood",
             "blurb": "Alexa's 13-second masterclass in fake gore: press a flesh-toned wound piece onto each cheek, blend and shade the edges until it reads as torn skin, then let the fake blood run. The finished gashes look straight out of a slasher — and the prop-hammer reveal at the end sells the joke. Her caption just says 'super easy,' and for once it's true. Tap the video and watch it come together.",
             "source": "Alexa (@aleee.rbb)", "url": "https://www.tiktok.com/@aleee.rbb/video/7696632427116170526", "tt": "7696632427116170526"},
            {"name": "Hello Kitty × Ghostface Custom Mask — V02", "who": "Adults & teens", "difficulty": "Hard", "time": "A weekend or more",
             "materials": "A sculpted mask base, white paint, black for the eyes and whiskers, yellow for the nose, and one big red bow — the finished piece is all in the video",
             "blurb": "The sweetest face in horror: mask maker CartoonDeadwork's Hello Kitty × Ghostface custom mask, brought back from the dead as V02 — red bow, whiskers and all. He even hid a Golden Coin out there somewhere: find it and you claim a custom mask of your own. Tap the video and watch it come back to life.",
             "source": "CartoonDeadwork (@k2theministry)", "url": "https://www.tiktok.com/@k2theministry/video/7688545412717825293", "tt": "7688545412717825293"},
            {"name": "Silent Hill Nurse Costume — Full DIY Tutorial", "who": "Adults & teens", "difficulty": "Medium", "time": "An afternoon or more",
             "materials": "A nurse dress or scrubs to distress, mask-making basics — her full tutorial walks through every piece she uses",
             "blurb": "Eimi's start-to-finish tutorial for her Silent Hill nurse — the bandaged Dark Nurse look from the games and films, distressed and bloodied by hand. She wants to see as many Silent Hill nurses out there this Halloween as possible: tap the photo, press play, and build yours along with her.",
             "source": "@eimi.wordt.dutchie", "url": "https://www.tiktok.com/@eimi.wordt.dutchie/video/7695321330354359584",
             "ttf": "7695321330354359584", "ttf_thumb": "/static/img/silenthill_nurse_costume.jpg"},
            {"name": "DIY Groot Costume from Foam Pipe Insulation", "who": "Adults & teens", "difficulty": "Hard", "time": "A weekend or more",
             "materials": "Foam pipe insulation tubes, hot glue, brown and grey paint for the bark finish, moss or faux greenery for the sprouts",
             "blurb": "Danielle built a full Groot out of hardware-store foam pipe insulation — twisted foam tubes become the vine-like limbs and bark body, moss and all. Her Groot broke the internet years ago and she still calls it one of her favorite homemade costumes. Tap the photo to watch the reel.",
             "source": "Danielle | DIY + DESIGN (@themindfulhaven)", "url": "https://www.instagram.com/reel/Dew32sWMjd8/",
             "ig": "Dew32sWMjd8", "ig_thumb": "/static/img/groot_costume_reel.jpg"},
        ],
    },
    {
        "id": "kids",
        "title": "&#x1F383; For Kids",
        "sub": "Weekend projects and after-school builds — cardboard, felt and a glue gun go a long way.",
        "ideas": [
            {"name": "Cardboard Robot", "who": "Kids 5–10", "difficulty": "Easy", "time": "About 2 hours",
             "materials": "Two cardboard boxes, foil or silver tape, bottle caps, dryer ducting, glow sticks",
             "blurb": "The classic box robot, upgraded: light-up trim, a LEGO-style control panel and glow-in-the-dark cuffs so your little bot stays visible after dark.",
             "source": "Goodnight Fox", "url": "https://www.goodnightfox.com/blog/robot-costume", "pin": "862580134928461179"},
            {"name": "Umbrella Jellyfish", "who": "Kids 4+", "difficulty": "Easy", "time": "About 30 minutes",
             "materials": "Clear or white umbrella, bubble wrap, ribbon scraps, light-colored outfit",
             "blurb": "A clear umbrella becomes the jellyfish bell and the ribbons do the floating — a showstopper that weighs almost nothing and needs zero sewing.",
             "source": "PSECU", "url": "https://www.psecu.com/learn/6-easy-diy-halloween-costumes-for-kids", "pin": "755619643778031009"},
            {"name": "Lion Rainsuit Costume", "who": "Toddlers & kids", "difficulty": "Easy", "time": "About 45 minutes",
             "materials": "Yellow rainsuit or sweatsuit, brown or tan fleece for the mane, a hood or hat, hot glue or safety pins",
             "blurb": "A roar you can wear in the rain: a yellow rain set turns into a lion with a fluffy fleece mane on the hood. No-sew, puddle-proof, and the pin photo above is the real finished costume.",
             "source": "Jan & Jul", "url": "https://janandjul.com/easy-halloween-costumes/", "pin": "867928159436914451"},
            {"name": "Astronaut Space Suit", "who": "Kids 4–9", "difficulty": "Easy", "time": "About 1–2 hours",
             "materials": "Clear plastic globe or bucket for the helmet, white sweats, two recycled bottles, cardboard, silver tape and paint",
             "blurb": "Goodnight Fox's no-sew space suit — a globe helmet, a recycled-bottle jetpack and hand-drawn mission patches. The same creator as the robot above, and just as cardboard-friendly.",
             "source": "Goodnight Fox", "url": "https://sprout.goodnightfox.com/activity/astronaut-costume", "pin": "695454367515339795"},
            {"name": "Pink Light-Up Witch", "who": "Kids 3–7", "difficulty": "Medium", "time": "An afternoon",
             "materials": "Pink and silver fabric, tulle for the skirt, elastic waistband, a witch hat, battery string lights",
             "blurb": "Not every witch wears black: this one layers a shimmery pink-and-silver skirt and lights it up for after-dark visibility. Sweet, spooky, and very easy to spot in a crowd.",
             "source": "Goodnight Fox", "url": "https://sprout.goodnightfox.com/activities/pink-witch-costume", "pin": "416442296825062489"},
            {"name": "Cute Clown Costumes (Under $10)", "who": "Kids & adults", "difficulty": "Easy", "time": "About 30 minutes",
             "materials": "Bright closet basics, pom-poms, suspenders or a bow tie, face paint, a yarn wig or party hat",
             "blurb": "Melanie from Simple Made Pretty builds a whole clown look for under ten bucks — thrift finds, pom-pom buttons and face paint. Tap the video and she walks you through it.",
             "source": "Simple Made Pretty", "url": "https://www.youtube.com/watch?v=7-wB3hUV1s0", "yt": "7-wB3hUV1s0"},
        ],
    },
    {
        "id": "adults",
        "title": "&#x1F9DB; For Adults",
        "sub": "Closet-first costumes and pun costumes that land at the party — most start with clothes you already own.",
        "ideas": [
            {"name": "Wednesday Addams", "who": "Adults & teens", "difficulty": "Easy", "time": "Under 1 hour",
             "materials": "Black dress with white collar (or layered shirt), pale makeup, black eyeliner, braids or a wig",
             "blurb": "From London Mums' budget homemade-outfits roundup: deadpan is the whole costume. Pale base, a widow's-peak eyeliner flick, two braids, and your most miserable expression.",
             "source": "London Mums Magazine", "url": "https://www.londonmumsmagazine.com/whats-on/activities/get-creative/simple-homemade-halloween-outfits-hairdos-on-a-budget/", "pin": "169377635982127789"},
            {"name": "Cereal Killer", "who": "Adults", "difficulty": "Easy", "time": "About 1 hour",
             "materials": "White tee, mini cereal boxes, cardboard knives, red paint, duct tape, marker",
             "blurb": "The pun costume that never dies: cereal boxes and cardboard cutlery taped to a tee, finished with a tasteful amount of 'blood' splatter. Marc and Mandy demo it in their video segment.",
             "source": "Marc and Mandy", "url": "https://marcandmandy.com/easy-cheap-diy-halloween-costumes/", "yt": "FuPT1SYOyi0"},
            {"name": "Gumball Machine Costume", "who": "Adults & teens", "difficulty": "Easy", "time": "About 1 hour",
             "materials": "Pom-pom balls, a strap top or tank, red skirt, headband, cardstock for the 25¢ slot",
             "blurb": "DIY Joy's candy-machine classic: pom-poms glued over a top, a red skirt as the machine base, and a hand-drawn quarter slot to finish it. Insert coin, become the costume.",
             "source": "DIY Joy", "url": "https://diyjoy.com/easy-diy-gumball-machine-costume/", "pin": "292593307067691850"},
            {"name": "Optical-Illusion Costume", "who": "Adults & teens", "difficulty": "Medium", "time": "An afternoon",
             "materials": "A base outfit to build the illusion on — her video walks through the whole rig and lists every piece she uses",
             "blurb": "Wyld Woods DIY's brand-new optical-illusion build: the kind of costume that makes people look twice, then ask how you did it. Tap the video and she walks the whole trick, start to finish.",
             "source": "Wyld Woods DIY (@wyldwoodsdiy)", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7700739541933493517", "tt": "7700739541933493517"},
        ],
    },
    {
        "id": "couples",
        "title": "&#x1F491; Couples & Groups",
        "sub": "Matching looks that are twice the fun and (mostly) half the effort each.",
        "ideas": [
            {"name": "Harry & Hermione", "who": "Couples", "difficulty": "Easy", "time": "A day or two of gathering pieces",
             "materials": "White collared shirts, gray sweaters, house ties and patches, wands, round glasses, eyeliner (for the scar)",
             "blurb": "The closet-cosplay classic that once won a Best Couple Costume prize — uniforms from your own wardrobe plus a few cheap accessories.",
             "source": "Journey With J", "url": "https://www.journeywithjblog.com/harry-hermione-diy-halloween-costumes/", "pin": "763360205581479639"},
            {"name": "Scarecrow Couple", "who": "Couples & families", "difficulty": "Easy", "time": "About 1–2 hours",
             "materials": "Flannel shirts, jeans or a dress, raffia or straw, burlap patches, straw hats, rope belt",
             "blurb": "Cozy fall energy for two: patched flannel, raffia 'straw' at the cuffs, and a sunflower or faux-corn prop to sell the harvest look.",
             "source": "Simple Made Pretty", "url": "https://simplemadepretty.com/halloween-couples-costumes/", "pin": "507710558016966696"},
            {"name": "Giant Waffle & Eleven", "who": "Couples, siblings, parent + kid", "difficulty": "Medium", "time": "An afternoon",
             "materials": "Cardboard, yellow paint, yellow pool noodle, straps, red foam sheet",
             "blurb": "One of you is a giant Eggo — pool-noodle strips make the waffle grid — and the other just needs a pink dress and a box of the real thing.",
             "source": "See Kate Sew", "url": "https://seekatesew.com/how-to-make-a-waffle-costume-diy-eggo-costume/", "pin": "20055160832141638"},
            {"name": "Piñata & Candy Duo", "who": "Couples & friends", "difficulty": "Medium", "time": "About 2 hours",
             "materials": "Crepe paper or streamers in rainbow colors, a plain outfit to cover, cardboard, a toy bat, candy props",
             "blurb": "One of you is the piñata — layered crepe-paper fringe over a base outfit — and the other is the candy, toy bat optional. DIY Joy's duo is a party photo waiting to happen.",
             "source": "DIY Joy", "url": "https://diyjoy.com/easy-diy-pinata-and-candy-costume/", "pin": "292593307067588946"},
            {"name": "Aladdin & Genie Family Costumes", "who": "Couples & families", "difficulty": "Easy", "time": "An afternoon of gathering pieces",
             "materials": "Blue outfit with a gold sash and a lamp prop (genie), vest, white pants and a cap (Aladdin)",
             "blurb": "Jenn Hallak's family let their daughter pick the theme and she chose a whole new world: a genie in blue and gold, an Aladdin, and a magic lamp to finish the story.",
             "source": "Jenn Hallak", "url": "https://jennhallak.com/blog/family-halloween-costumes-aladdin-jasmine", "pin": "266345765460225348"},
        ],
    },
    {
        "id": "last-minute",
        "title": "&#x23F0; Last-Minute & No-Sew",
        "sub": "It's October 31st and you have a glue gun (or not even that). Start here.",
        "ideas": [
            {"name": "No-Sew Felt Strawberry", "who": "Kids & adults", "difficulty": "Easy", "time": "About 1 hour",
             "materials": "Red and green felt, fabric glue, a plain tee, fabric scissors, ruler",
             "blurb": "Felt, glue, zero stitches: a poncho-style berry body with a leafy collar and seed details, sized off a T-shirt you already have.",
             "source": "DIY Joy", "url": "https://diyjoy.com/easy-diy-halloween-costume-ideas/", "pin": "292593307067646357"},
            {"name": "50s Statement Costume", "who": "Adults", "difficulty": "Easy", "time": "About 30 minutes",
             "materials": "Thrifted dress or tee-and-jeans, a bandana, red lipstick, cat-eye liner",
             "blurb": "DIY Joy's retro standby: a tight front roll in your hair, a bandana, red lips and cat-eye liner — most of it is already in your closet or one thrift bin away.",
             "source": "DIY Joy", "url": "https://diyjoy.com/50s-costume/", "pin": "292593307067660073"},
            {"name": "36 Last-Minute Costume Ideas", "who": "Kids, adults & couples", "difficulty": "Easy", "time": "5–60 minutes each",
             "materials": "Whatever the closet gives you — the runaway bride in the photo started as a dress and a veil",
             "blurb": "Thirty-six closet-first rescues from DIY Joy, from a runaway bride to five-minute pun costumes. When it's October 31st at 4 p.m., start here.",
             "source": "DIY Joy", "url": "https://diyjoy.com/last-minute-diy-halloween-costumes/", "pin": "292593307047942812"},
        ],
    },
    {
        "id": "scary",
        "title": "&#x1F9DF; Scary & Makeup-Led",
        "sub": "The costume is the makeup: wounds, bites and face paint that do the heavy lifting.",
        "ideas": [
            {"name": "Half-Zombie Makeup", "who": "Adults & teens", "difficulty": "Medium", "time": "About 45 minutes",
             "materials": "Pale foundation, liquid latex or tissue-and-glue, fake blood, dark eyeshadow",
             "blurb": "Half beauty, half bitten: one side stays glam while the other side rots. From DIY Joy's Halloween makeup tutorials collection — the split-face contrast is what makes it terrifying.",
             "source": "DIY Joy", "url": "https://diyjoy.com/best-halloween-makeup-tutorials", "pin": "292593307067525168"},
            {"name": "Creepy Doll Makeup", "who": "Adults & teens", "difficulty": "Medium", "time": "About 45 minutes",
             "materials": "Foundation, white eyeliner, false lashes, heavy blush, heart-shaped lipstick, a lace dress or collar",
             "blurb": "Big round eyes, rosy cheeks and tiny heart lips — the makeup IS the costume. DIY Joy's doll look is pretty until you hold the stare a second too long.",
             "source": "DIY Joy", "url": "https://diyjoy.com/diy-doll-halloween-makeup/", "pin": "292593307067659575"},
            {"name": "Full Face of Googly Eyes", "who": "Adults & teens", "difficulty": "Medium", "time": "About 30–45 minutes",
             "materials": "Craft googly eyes in mixed sizes, skin-safe adhesive or lash glue, black base makeup or a dark hood",
             "blurb": "Julia at Cuckoo4Design glued real googly eyes over her whole face — and it gets creepier when she moves and they all shift. Simple, unforgettable, mildly upsetting.",
             "source": "Cuckoo4Design", "url": "https://cuckoo4design.com/diy-full-face-of-googly-eyes-makeup/", "pin": "228065168626114409"},
        ],
    },
]


@app.get("/diy-costumes", response_class=HTMLResponse)
def diy_costumes_page(request: Request):
    return templates.TemplateResponse(
        request, "diy_costumes.html", {"sections": COSTUME_SECTIONS},
    )


# ------------------------------------------------------------- haunt or not

DUEL_EXCLUDE_IDS = frozenset({197, 210, 228, 235, 239, 244, 245, 246, 250, 251, 253, 260, 265, 270, 278, 279, 280, 282, 283, 284, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 924, 925, 926, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1273, 1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2064, 2073, 2081, 2082, 2084, 2094, 2098, 2100, 2101, 2104, 2106, 2107, 2108, 2109, 2110, 2112, 2119, 2120, 2121, 2122, 2126, 2127, 2130, 2131, 2133, 2134, 2135, 2136, 2137, 2140, 2142, 2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2155, 2156, 2160, 2162, 2168, 2169, 2170, 2172, 2174, 2178, 2179, 2181, 2182, 2186, 2193, 2199, 2202, 2204, 2205, 2206, 2208, 2209, 2211, 2214, 2217, 2221, 2226, 2227, 2228, 2230, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239, 2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2251, 2252, 2253, 2254, 2255, 2256, 2257, 2258, 2259, 2260, 2261, 2262, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271, 2272, 2273, 2274, 2275, 2276, 2277, 2280, 2284, 2288, 2291, 2292, 2293, 2294, 2295, 2296, 2300, 2302, 2311, 2312, 2313, 2315, 2320, 2321, 2322, 2323, 2324, 2327, 2328, 2329, 2330, 2332, 2333, 2334, 2335, 2336, 2337, 2338, 2340, 2341, 2343, 2347, 2348, 2350, 2352, 2359, 2363, 2364, 2365, 2366, 2367, 2368, 2369, 2371, 2374, 2375, 2376, 2377, 2379, 2380, 2381, 2386, 2389, 2397, 2398, 2399, 2404, 2405, 2406, 2412, 2417, 2418, 2420, 2421, 2422, 2423, 2431, 2432, 2438, 2440, 2441, 2443, 2444, 2446, 2449, 2450, 2455, 2457, 2460, 2463, 2465, 2470, 2475, 2476, 2478, 2479, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2490, 2491, 2492, 2493, 2494, 2495, 2497, 2498, 2499, 2500, 2501, 2502, 2505, 2506, 2507, 2508, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2531, 2533, 2534, 2537, 2539, 2540, 2541, 2542, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559, 2560, 2561, 2562, 2563, 2564, 2575, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2590, 2591, 2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2635, 2636, 2637, 2638, 2639, 2640, 2644, 2646, 2649, 2656, 2659, 2662, 2668, 2669, 2670, 2671, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2684, 2686, 2687, 2688, 2691, 2694, 2695, 2699, 2700, 2701, 2702, 2703, 2704, 2705, 2707, 2708, 2709, 2710, 2711, 2712, 2715, 2716, 2717, 2718, 2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2746, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767, 2770, 2771, 2772, 2773, 2774, 2777, 2778, 2779, 2782, 2783, 2784, 2786, 2787, 2788, 2790, 2794, 2795, 2796, 2797, 2798, 2799, 2801, 2802, 2803, 2805, 2807, 2811, 2812, 2813, 2814, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2828, 2832, 2833, 2834, 2835, 2836, 2837, 2839, 2842, 2843, 2845, 2847, 2848, 2854, 2855, 2856, 2857, 2860, 2862, 2863, 2864, 2866, 2870, 2871, 2872, 2874, 2876, 2877, 2879, 2880, 2881, 2886, 2888, 2889, 2890, 2891, 2893, 2894, 2896, 2898, 2900, 2901, 2902, 2905, 2907, 2908, 2909, 2910, 2911, 2912, 2914, 2915, 2916, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927, 2928, 2929, 2931, 2932, 2933, 2934, 2935, 2937, 2938, 2939, 2940, 2941, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2964, 2965, 2968, 2969, 2970, 2974, 2975, 2976, 2978, 2979, 2980, 2981, 2982, 2983, 2986, 2987, 2988, 2989, 2991, 2992, 2998, 2999, 3000, 3003, 3004, 3006, 3007, 3009, 3010, 3011, 3013, 3014, 3015, 3016, 3017, 3019, 3020, 3025, 3026, 3034, 3035, 3036, 3039, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3057, 3058, 3059, 3060, 3061, 3062, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3076, 3077, 3082, 3083, 3085, 3086, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3108, 3109, 3110, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3132, 3134, 3135, 3137, 3138, 3139, 3144, 3145, 3146, 3147, 3148, 3149, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3161, 3162, 3163, 3164, 3165, 3169, 3170, 3171, 3172, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3186, 3188, 3189, 3190, 3191, 3192, 3195, 3196, 3197, 3202, 3203, 3210, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3240, 3241, 3242, 3243, 3244, 3245, 3246, 3247, 3248, 3254, 3256, 3257, 3258, 3260, 3261, 3266, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3278, 3279, 3280, 3282, 3283, 3288, 3289, 3290, 3291, 3292, 3293, 3295, 3297, 3299, 3300, 3301, 3302, 3303, 3304, 3305, 3312, 3314, 3319, 3320, 3324, 3325, 3326, 3327, 3332, 3333, 3334, 3336, 3337, 3338, 3340, 3343, 3346, 3348, 3352, 3353, 3354, 3355, 3356, 3357, 3359, 3360, 3361, 3362, 3364, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3379, 3380, 3382, 3385, 3387, 3388, 3390, 3391, 3394, 3397, 3398, 3402, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423, 3424, 3427, 3428, 3429, 3432, 3435, 3438, 3439, 3443, 3444, 3445, 3447, 3449, 3450, 3451, 3453, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3466, 3474, 3477, 3482, 3484, 3485, 3489, 3490, 3492, 3497, 3498, 3500, 3501, 3502, 3504, 3506, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3521, 3522, 3523, 3524, 3527, 3529, 3531, 3532, 3537, 3540, 3545, 3546, 3548, 3551, 3552, 3554, 3555, 3556, 3559, 3568, 3570, 3571, 3572, 3573, 3620, 3636, 3667, 3673, 3674, 3724, 3741, 3911, 3925, 3936, 3938, 3993, 4014, 4053, 4058, 4077, 4488, 4489, 4491, 4493, 4494, 4496, 4498, 4500, 4502, 4503, 4505, 4507, 4509, 4511, 4513, 4514, 4516, 4518, 4520, 4522, 4523, 4525, 4527, 4529, 4531, 4532, 4534, 4536, 4538, 4540, 4542, 4543, 4545, 4547, 4549, 4551, 4553, 4555, 4798, 4800, 4802, 4804, 4806, 4808, 4810, 4811, 4812, 4813, 4814, 4815, 4816, 4817, 4818, 4819, 4820, 4821, 4822, 4823, 4824, 4825, 4826, 4827, 4828, 4829, 4830, 4831, 4832, 4833, 4839, 4841, 4843, 4844, 4846, 4848, 4850, 4851, 4853, 4855, 4856, 4978, 4986, 4989, 5067, 5071, 5073, 5074, 5075, 5080, 5082, 5083, 5085, 5086, 5087, 5088, 5089, 5092, 5093, 5094, 5096, 5097, 5098, 5099, 5100, 5101, 5102, 5105, 5524, 5525, 5526, 5527, 5528, 5529, 5530, 5531, 5532, 5533, 5534, 5535, 5536, 5538, 5648})  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)

DUEL_TABLE_SQL = (
    "CREATE TABLE IF NOT EXISTS duel_stats "
    "(entry_id INTEGER PRIMARY KEY, wins INTEGER DEFAULT 0, battles INTEGER DEFAULT 0)"
)


def _duel_slim(e: dict) -> dict:
    return {
        "id": e["id"],
        "title": e["title"],
        "town": e["town_label"],
        "scare": e.get("scare_level") or "",
        "img": e["thumb_url"] or e["media_url"],
    }


@app.get("/haunt-or-not", response_class=HTMLResponse)
def haunt_or_not_page(request: Request):
    with get_conn(DB_PATH) as conn:
        conn.execute(DUEL_TABLE_SQL)
        rows = conn.execute(
            """SELECT e.id, e.title, e.town, s.wins, s.battles
               FROM duel_stats s JOIN entries e ON e.id = s.entry_id
               WHERE s.battles >= 3
               ORDER BY (CAST(s.wins AS FLOAT) / s.battles) DESC, s.battles DESC
               LIMIT 10"""
        ).fetchall()
    leaders = []
    for r in rows:
        d = dict(r)
        d["town_label"] = extract_city_state(d["town"] or "") or d["town"] or ""
        d["winpct"] = round(100 * d["wins"] / d["battles"]) if d["battles"] else 0
        leaders.append(d)
    return templates.TemplateResponse(
        request, "haunt_or_not.html", {"leaders": leaders},
    )


# ------------------------------------------------------- portal catalog
# PORTAL CATALOG (Dan, Oct 26: "Let's add more games as well" — the
# "portal catalog later" half of his Oct 25 "Both — ours first, portal
# catalog later" call).
#
# Oct 26 SWAP (Dan: "Swap the Arcade to ungated games now"): the
# original route was GameDistribution's publisher program, but GD
# REJECTED HauntMap's publisher registration on traffic grounds the
# same day, and its embeds render GD's "NOT AVAILABLE HERE"
# interstitial on gethauntmap.com — the domain was never approved,
# so no GD title can ever play here. The shelf now runs on GamePix's
# open webmaster embed program: embedding catalog games on
# third-party sites IS the product, there is no domain approval or
# publisher-account gate, games are hosted + ad-monetized by GamePix,
# and each embed is play.gamepix.com/<slug>/embed?sid=<publisher id>
# (portal_games.js builds the URL; the sid is the one GamePix
# distributes in its public demo feed — swap in HauntMap's own free
# GamePix sid in portal_games.js if attribution is ever wanted).
# CrazyGames stays ruled out: developer-submission portal, games
# sitelocked to crazygames.com, no third-party embed program.
#
# Curation rules applied: Halloween/horror/spooky only, family-
# appropriate (no gore FPS), touch-first controls (most traffic is
# phones), instantly playable. Genre-for-genre swap against the GD
# shelf (bubble / knife timing / tower defense / merge / match-3 /
# memory / hidden object / coloring). Cover art is GamePix's own
# img CDN (the facade role GD's img CDN played before). Ghost Maze
# stays the featured hero above this section; nothing here touches
# it or its leaderboard.
#
# RENDER-VERIFIED Oct 26 (live-browser play-through, each embed
# taken past the GamePix splash into real gameplay — see
# hidden_files/arcade-swap-prep/VERIFIED.md). Three prep candidates
# were caught bad and replaced: knife-hit-horror-2 (loaded a
# different game), spooky-bubble-shooter (game file Access Denied),
# halloween-match / zombie-gems (wrong gameplay / wrong game).
# Aspect w/h per GamePix feed metadata + the verification pass.
#
# iPHONE GAMES RULE (Dan, Oct 27: "Don't feature games on the iPhone
# that won't play on the iPhone"). Every embeddable game carries an
# "iphone" flag. Audit of the 12 GamePix titles (arcade + ninja,
# Oct 27, 2026): ALL 12 verdict PLAYS ON IPHONE — evidence per title:
# GamePix catalog feed touch=true + responsive=true (where the title
# appears in the feed) and GamePix's own game page JSON-LD
# availableOnDevice includes "Mobile" with a Mobile platform line
# (all 12 checked individually); every control scheme is pointer-
# native (tap / drag / swipe — no keyboard-only title in the set).
# Weakest file: chaos-zombie-tower-defense, whose How-to-Play text is
# mouse-worded ("played entirely with the mouse", drag & drop) — it
# still carries GamePix's Mobile platform listing and its mechanic is
# pointer drag, which HTML5 touch handles natively. Ghost Maze (first
# party) also PLAYS: swipe-on-stage + an on-screen D-pad (pointerdown)
# ship in ghost_maze.js next to the keyboard controls. Because no
# current title fails, every flag below ships True and the iOS
# demotion in games.html (data-iphone="0" cards sink below the
# "Plays best on a computer or tablet" divider, never featured) is
# armed but invisible today. CLASSIFYING A NEW TITLE: set "iphone"
# only after the same three checks (catalog touch flag, vendor page
# Mobile listing, vendor-documented touch controls); if any check
# fails or is unverifiable, ship the flag False — it will still list
# on desktop and sink on iPhone.
PORTAL_GAMES = [
    {"iphone": True, "slug": "halloween-bubble-shooter",
     "img": "https://img.gamepix.com/games/halloween-bubble-shooter/cover/halloween-bubble-shooter.png?w=512",
     "title": "Halloween Bubble Shooter",
     "blurb": "Aim, match and pop the monster bubbles. Tap, drag, "
              "release — pure Halloween candy for your brain.",
     "tag": "Bubble shooter \u00b7 all ages", "w": 600, "h": 800},
    {"iphone": True, "slug": "knife-hit",
     "img": "https://img.gamepix.com/games/knife-hit/cover/knife-hit.png?w=512",
     "title": "Knife Hit",
     "blurb": "Throw knives, split the targets, beat the boss. "
              "One-tap timing that gets dangerously addictive.",
     "tag": "Arcade timing", "w": 800, "h": 600},
    {"iphone": True, "slug": "chaos-zombie-tower-defense",
     "img": "https://img.gamepix.com/games/chaos-zombie-tower-defense/cover/chaos-zombie-tower-defense.png?w=512",
     "title": "Chaos Zombie Tower Defense",
     "blurb": "Tower defense: build your line, hold the gate, "
              "zap and freeze the horde, survive the night.",
     "tag": "Tower defense", "w": 800, "h": 600},
    {"iphone": True, "slug": "spooky-merge",
     "img": "https://img.gamepix.com/games/spooky-merge/cover/spooky-merge.png?w=512",
     "title": "Spooky Merge",
     "blurb": "Drop the spooky pieces and merge your way up the "
              "chain — pumpkins, ghosts and monsters combine into "
              "bigger and bigger haunts.",
     "tag": "Merge puzzle \u00b7 portrait play", "w": 600, "h": 800},
    {"iphone": True, "slug": "jewel-monsters",
     "img": "https://img.gamepix.com/games/jewel-monsters/cover/jewel-monsters.png?w=512",
     "title": "Jewel Monsters",
     "blurb": "Match-3 with a monstrous twist — line up the "
              "jewel monsters and chain the combos.",
     "tag": "Match-3 puzzle \u00b7 portrait play", "w": 600, "h": 800},
    {"iphone": True, "slug": "halloween-matching",
     "img": "https://img.gamepix.com/games/halloween-matching/cover/halloween-matching.png?w=512",
     "title": "Halloween Matching",
     "blurb": "Flip the tiles and match the monsters — "
              "concentration candy for sharp little ghouls.",
     "tag": "Memory \u00b7 kids love it", "w": 800, "h": 600},
    {"iphone": True, "slug": "spooky-halloween-hidden-pumpkin",
     "img": "https://img.gamepix.com/games/spooky-halloween-hidden-pumpkin/cover/spooky-halloween-hidden-pumpkin.png?w=512",
     "title": "Spooky Halloween Hidden Pumpkin",
     "blurb": "Hidden-object hunt: spot every hidden pumpkin "
              "haunting the spooky scenes before the clock runs out.",
     "tag": "Hidden object", "w": 800, "h": 600},
    {"iphone": True, "slug": "halloween-coloring-book-for-kids",
     "img": "https://img.gamepix.com/games/halloween-coloring-book-for-kids/cover/halloween-coloring-book-for-kids.png?w=512",
     "title": "Halloween Coloring Book",
     "blurb": "Color the witches, cats and jack-o\u2019-lanterns — "
              "the calm corner of the arcade.",
     "tag": "Coloring \u00b7 all ages", "w": 800, "h": 600},
]


# ------------------------------------------------- lego ninjago shelf
# LEGO NINJAGO GAMES (Dan, Oct 27: "Can we ninjago video games to the
# games?"). IP-clean by construction: HauntMap hosts NOTHING here — no
# game files, no ripped assets. Every card is a LINK-OUT to the game's
# official page on LEGO.com for Kids (kids.lego.com), with cover art
# hotlinked from LEGO's own CDN (the same facade role GamePix's img
# CDN plays for the Arcade shelf above).
#
# EMBEDS ARE NOT AN OPTION: verified Oct 27, every kids.lego.com game
# page sends `x-frame-options: SAMEORIGIN`, so iframing them anywhere
# else is blocked by LEGO itself. Link-out cards are the only legal +
# working shape. All eight titles below were verified LIVE in LEGO's
# official kids games catalog on Oct 27, 2026 (slugs carry LEGO's own
# content ids; Ninjago: The Quest is the current hub adventure).
#
# Deliberately NOT here: the big console titles (The LEGO NINJAGO
# Movie Video Game, Shadow of Ronin, LEGO Brawls) — /games is a
# tap-and-play page, and this shelf is playable-web-games only.
NINJAGO_GAMES = [
    {"title": "NINJAGO: The Quest",
     "url": "https://kids.lego.com/en-us/games/ninjago-the-quest",
     "img": "https://www.lego.com/cdn/cs/kids-lego-com/assets/bltbdabe1629e7416bd/SEO_Image.png?crop=1200%3A630&format=jpg",
     "blurb": "LEGO's newest Ninjago adventure — journey across the "
              "Merged Lands, sharpen your Spinjitzu and save the "
              "Realms from the forces of evil.",
     "tag": "Adventure · free on LEGO.com"},
    {"title": "Fear No Chaos",
     "url": "https://kids.lego.com/en-us/games/fear-no-chaos-f6f0a617bc2e46d28a38361a2fba7a16",
     "img": "https://www.lego.com/cdn/cs/kids-lego-com/assets/blt126653566dd96767/fear_no_chaos.png?crop=1200%3A630&format=jpg",
     "blurb": "The 2025 Dragons Rising game: stand with Arin, Sora "
              "and Wyldfyre and face down the chaos — fear no chaos.",
     "tag": "Action · free on LEGO.com"},
    {"title": "Crystalized",
     "url": "https://kids.lego.com/en-us/games/crystalized-37ece4e897344e6ab1e570158611c3a2",
     "img": "https://www.lego.com/cdn/cs/kids-lego-com/assets/bltc84802ea5a9be742/crystalized.png?crop=1200%3A630&format=jpg",
     "blurb": "The Crystal King is marching on Ninjago City — "
              "crystalize your courage and defend the city with the "
              "whole ninja team.",
     "tag": "Battle · free on LEGO.com"},
    {"title": "Ninja Unite!",
     "url": "https://kids.lego.com/en-us/games/ninja-unite-977ee66c38be4157a51decaebd01e9bd",
     "img": "https://www.lego.com/cdn/cs/kids-lego-com/assets/bltf38eb0ff0e51eabf/ninja_unite.jpg?crop=1200%3A630&format=jpg",
     "blurb": "Ninja are stronger together: unite Kai, Lloyd, Jay, "
              "Cole, Zane and Nya and take the fight to the bad guys "
              "as one team.",
     "tag": "Team action · free on LEGO.com"},
    {"title": "Chen's Return",
     "url": "https://kids.lego.com/en-us/games/chens-return-c471618a72688352875c53cc0d66a47e",
     "img": "https://www.lego.com/cdn/cs/kids-lego-com/assets/blt1e5525c0629d49ab/chens-return.jpg?crop=1200%3A630&format=jpg",
     "blurb": "Master Chen is back and up to his old tricks — battle "
              "through his island of traps, snakes and henchmen.",
     "tag": "Action · free on LEGO.com"},
    {"title": "Golden Legacy",
     "url": "https://kids.lego.com/en-us/games/golden-legacy-d346fc1d92084519bbcb3c39c549d41f",
     "img": "https://www.lego.com/cdn/cs/kids-lego-com/assets/bltda4e097d78850503/ninjago_golden_legacy.png?crop=1200%3A630&format=jpg",
     "blurb": "A golden celebration of Ninjago's greatest hits — "
              "replay classic moments from the early seasons in "
              "shining Legacy style.",
     "tag": "Classics · free on LEGO.com"},
    {"title": "Prime Empire",
     "url": "https://kids.lego.com/en-us/games/prime-empire-f98e88849512c6f12bb01678c9ce6c65",
     "img": "https://www.lego.com/cdn/cs/kids-lego-com/assets/bltfed6decfa8075a71/prime_empire.jpg?crop=1200%3A630&format=jpg",
     "blurb": "Step INSIDE the Prime Empire video game — race, "
              "fight and level up through the arcade world from "
              "Season 12. Don't let Unagami win.",
     "tag": "Arcade adventure · free on LEGO.com"},
    {"title": "What Would a Ninja Do?",
     "url": "https://kids.lego.com/en-us/games/what-would-a-ninja-do-8dc2552267354847aeac8bee5e1ed63d",
     "img": "https://www.lego.com/cdn/cs/kids-lego-com/assets/blt32b34e0d5cd2814d/what_would_a_ninja.jpg?crop=1200%3A630&format=jpg",
     "blurb": "Quick-fire ninja dilemmas: a tricky moment pops up "
              "and you decide — what would a ninja do? Think like "
              "a master.",
     "tag": "Quiz · free on LEGO.com"},
]


# ------------------------------------------------- ninja games shelf
# NINJA GAMES (Dan, Oct 27, scope expansion: "lets put any ninja games
# you can find on there as well"). Same IP discipline as the Ninjago
# shelf — only channels that are legally clean for HauntMap:
#
# EMBEDS run on GamePix's open webmaster embed program — the exact
# channel the Halloween Arcade already ships on (embedding IS the
# product; games hosted + ad-monetized by GamePix; portal_games.js
# builds play.gamepix.com/<slug>/embed, cover art is GamePix's own
# img CDN). All four ninja titles below were pulled from GamePix's
# public catalog feed and embed-verified (HTTP 200) on Oct 27, 2026.
# Family-fit pass applied: cartoon pirates/bombs only, no gore.
#
# LINK-OUTS go to the creators' own itch.io pages (verified playable
# in-browser + family-fit on Oct 27, 2026). itch playable embeds are
# only clean when the creator shares an embed grant; that could not
# be cleanly verified per title (and one title warns Safari/Firefox
# may not run it), so — same call as the LEGO shelf — these ship as
# link-out cards, never iframes. Cover art is each creator's own
# itch CDN art.
#
# REJECTED (checked Oct 27, do not add): GameDistribution ninja
# titles (GD rejected HauntMap's publisher signup — embeds render
# their NOT AVAILABLE interstitial here); CrazyGames (sitelocked, no
# third-party embed program); itch fan clones of commercial games
# (a Sekiro remake, an 8-bit Strider clone — other studios' IP);
# itch titles off the family brief (Dojo of Death, JK Assassins,
# Drunk Ninja, HACKSLASH); every ROM/emulator and "free ninja games"
# clone-portal result (ripped files, no license chain).
NINJA_PORTAL_GAMES = [
    {"iphone": True, "slug": "angry-ninja",
     "img": "https://img.gamepix.com/games/angry-ninja/cover/angry-ninja.png?w=512",
     "title": "Angry Ninja",
     "blurb": "The pirates have picked the wrong island — help the "
              "Angry Ninjas bounce, slash and puzzle their way "
              "through every last one of them.",
     "tag": "Arcade · plays here via GamePix", "w": 480, "h": 320},
    {"iphone": True, "slug": "bighead-ninja",
     "img": "https://img.gamepix.com/games/bighead-ninja/cover/bighead-ninja.png?w=512",
     "title": "Bighead Ninja!",
     "blurb": "A big-headed ninja endless runner: sprint, leap and "
              "dodge as far as your little legs can carry you.",
     "tag": "Runner · plays here via GamePix", "w": 480, "h": 320},
    {"iphone": True, "slug": "block-ninja",
     "img": "https://img.gamepix.com/games/block-ninja/cover/block-ninja.png?w=512",
     "title": "Block Ninja",
     "blurb": "Two ninjas, one swipe at a time — steer both blocky "
              "ninjas up and down and thread them through the gaps.",
     "tag": "Swipe arcade · plays here via GamePix", "w": 480, "h": 320},
    {"iphone": True, "slug": "blow-out-bomb-blast-ninja",
     "img": "https://img.gamepix.com/games/blow-out-bomb-blast-ninja/cover/blow-out-bomb-blast-ninja.png?w=512",
     "title": "Blow Out Bomb Blast Ninja",
     "blurb": "Bombs away — slice the fuses and blow out every bomb "
              "before the clock (and the bomb) goes off.",
     "tag": "Arcade · plays here via GamePix", "w": 320, "h": 480},
]

NINJA_LINK_GAMES = [
    {"title": "Ninja Shurican",
     "byline": "by SnoutUp",
     "url": "https://snoutup.itch.io/shurican",
     "img": "https://img.itch.zone/aW1hZ2UvODM0My84MDk5MS5wbmc=/508x254%23mb/kzN3PH.png",
     "blurb": "Jump, slash and shuriken-throw your way through the "
              "horde — a fast little arcade ninja from the maker of "
              "Iron Snout.",
     "tag": "Play free on itch.io", "w": 508, "h": 254},
    {"title": "Ninja Cat (Classic)",
     "byline": "by cubee",
     "url": "https://cubeegames.itch.io/ninja-cat",
     "img": "https://img.itch.zone/aW1hZ2UvNzEzNzY2LzUwNjYyNjQucG5n/347x500/eKbgdB.png",
     "blurb": "A platformer about a ninja cat with a grappling hook. "
              "You have nine lives — make them count.",
     "tag": "Play free on itch.io", "w": 347, "h": 500},
    {"title": "Shelled Shinobi",
     "byline": "by magu",
     "url": "https://magu.itch.io/shelled-shinobi",
     "img": "https://img.itch.zone/aW1nLzE1MDkxNTUyLnBuZw==/original/ABnFAN.png",
     "blurb": "A turtle shinobi speedster: slide and bounce around "
              "in your shell at high speed, then pop out for precise "
              "jumps and quick turns.",
     "tag": "Play free on itch.io", "w": 480, "h": 270},
    {"title": "Sound Ninja",
     "byline": "by Kisiou",
     "url": "https://kisiou.itch.io/sound-ninja",
     "img": "https://img.itch.zone/aW1hZ2UvNTE1ODQ1MC8zMTI2NjQ2NS5wbmc=/347x500/o1b5SI.png",
     "blurb": "A rhythm ninja: the bamboo dances to the music, the "
              "beat throws you skyward — rotate, aim and slash on "
              "the rhythm.",
     "tag": "Play free on itch.io", "w": 347, "h": 500},
    {"title": "Nine Hole Ninja",
     "byline": "by Damon L. Wakes",
     "url": "https://damonwakes.itch.io/nine-hole-ninja",
     "img": "https://img.itch.zone/aW1hZ2UvMTkwOTk4MC8xMTIzMTQ0OC5wbmc=/347x500/hCjcqj.png",
     "blurb": "Ninja mini-golf! Nine holes of shuriken putting — "
              "the stealthiest sport on the fairway.",
     "tag": "Play free on itch.io", "w": 347, "h": 500},
    {"title": "Cherry Ninja",
     "byline": "by Hidebu Games",
     "url": "https://hidebu.itch.io/cherry-ninja",
     "img": "https://img.itch.zone/aW1nLzEzNzQyNjM0LnBuZw==/original/9aL9HZ.png",
     "blurb": "A cherry-blossom ninja dash under falling petals — "
              "quick, pretty and tougher than it looks. (Runs best "
              "in Chrome.)",
     "tag": "Play free on itch.io", "w": 480, "h": 270},
]


# ------------------------------------------- minecraft games shelf
# MINECRAFT GAMES (Dan, Oct 27: "Any Minecraft games?" — the shelf
# widened from a Dungeons headliner to the whole live Minecraft
# family). Same IP discipline as the LEGO shelf: LINK-OUT cards to
# official pages only, official art only, nothing hosted or ripped.
# Mojang/Microsoft does not offer a browser-playable Dungeons, so no
# card here pretends to embed a game; the one playable card is
# Minecraft Classic, Mojang's own free browser version, linked out
# (its tiny Azure shell serves no framing grant we rely on, and a
# keyboard WebGL game belongs full-screen anyway). Card art is each
# channel's own official art: Mojang's DAM key art for the
# minecraft.net cards, the Steam capsule from Valve's CDN, the
# TitledHeroArt from Microsoft's store catalog, the PS4 icon from
# PlayStation's image API — every URL curl-verified HTTP 200 with a
# gethauntmap.com Referer on Oct 27, 2026.
#
# Dungeons keeps the featured first seat — Dan named it first.
# Minecraft Dungeons II (released Sep 29, 2026) joins as the second
# card. CHECKED AND SKIPPED (dead/delisted, named so they are not
# re-added): Minecraft Earth (servers shut down June 2021) and
# Minecraft: Story Mode (delisted 2019, stores pulled).
MINECRAFT_GAMES = [
    {"title": "Minecraft Dungeons",
     "url": "https://www.minecraft.net/en-us/about-dungeons",
     "img": "https://www.minecraft.net/content/dam/minecraftnet/games/dungeons/key-art/Dungeons-PMP_Hero-Art_ParallaxB_1920x1080.jpg",
     "blurb": "The headliner: an action-RPG dungeon crawler set in "
              "the Minecraft world. Brave treasure-stuffed dungeons "
              "solo or with up to three friends, gear up with dozens "
              "of enchanted weapons and take down the evil "
              "Arch-Illager.",
     "tag": "Action RPG · E10+ · Official page",
     "go": "Official page", "w": 1920, "h": 1080, "featured": True},
    {"title": "Minecraft Dungeons II",
     "url": "https://www.minecraft.net/en-us/about-dungeons-ii",
     "img": "https://www.minecraft.net/content/dam/minecraftnet/games/spicewood/logos/Global-Header_Image-Tile_Dungeons-II_570x321.jpg",
     "blurb": "The brand-new sequel: drop the pickaxe, grab a sword. "
              "A new evil threatens two worlds at once and the "
              "dungeons are tougher than ever — charge in solo or "
              "with up to four players in co-op.",
     "tag": "New for 2026 · Official page",
     "go": "Official page", "w": 570, "h": 321},
    {"title": "Minecraft",
     "url": "https://www.minecraft.net/en-us/about-minecraft",
     "img": "https://www.minecraft.net/content/dam/minecraftnet/games/minecraft/key-art/About-Minecraft_Featured-Image-0_570x321.jpg",
     "blurb": "The one that started it all: build anything you can "
              "imagine block by block in Creative, or craft, gear up "
              "and survive the night in Survival. Java & Bedrock "
              "editions for PC, console and mobile.",
     "tag": "Sandbox · E10+ · Official page",
     "go": "Official page", "w": 570, "h": 321},
    {"title": "Minecraft Classic",
     "url": "https://classic.minecraft.net/",
     "img": "https://www.minecraft.net/content/dam/minecraftnet/games/minecraft/key-art/Global-Header_Image-Tile_Build-Worlds-Shape-Play_570x321.jpg.jpg",
     "blurb": "Mojang's freebie: the original 2009 Creative mode, "
              "playable free right in your browser — 32 classic "
              "blocks and pure nostalgia. You will need a keyboard.",
     "tag": "FREE in your browser · Official",
     "go": "Play free", "w": 570, "h": 321},
    {"title": "Minecraft Legends",
     "url": "https://www.minecraft.net/en-us/about-legends",
     "img": "https://www.minecraft.net/content/dam/minecraftnet/games/badger/key-art/Global-Header_Image-Tile_MC-Legends_570x321.jpg",
     "blurb": "Action-strategy in the Overworld: unite your allies, "
              "raise your banners and lead the charge to save the "
              "Overworld from the piglin invasion.",
     "tag": "Action strategy · Official page",
     "go": "Official page", "w": 570, "h": 321},
    {"title": "Minecraft Education",
     "url": "https://education.minecraft.net/en-us",
     "img": "https://education.minecraft.net/content/dam/education-edition/key-art/MCEDU_PropArt_15_1080x1080-1.png",
     "blurb": "The classroom edition: game-based learning with "
              "coding, chemistry and 600+ ready-made lessons, built "
              "for schools, camps and clubs.",
     "tag": "For classrooms · Official site",
     "go": "Official site", "w": 1080, "h": 1080},
]

# GET MINECRAFT DUNGEONS — the official store listings for the
# headliner (each card travels to that store; art is the store's own
# where the store serves it, Mojang's DAM key art for Nintendo,
# whose storefront renders its art client-side only).
MINECRAFT_DUNGEONS_STORES = [
    {"title": "Dungeons on Steam",
     "url": "https://store.steampowered.com/app/1672970/Minecraft_Dungeons/",
     "img": "https://shared.fastly.steamstatic.com/store_item_assets/steam/apps/1672970/capsule_616x353.jpg?t=1787063807",
     "blurb": "For PC on Steam: the base game, plus the Ultimate "
              "Edition with all six DLCs and the Ultimate DLC Bundle.",
     "tag": "PC · Steam", "go": "Steam store", "w": 616, "h": 353},
    {"title": "Dungeons on Xbox",
     "url": "https://www.xbox.com/en-us/games/store/minecraft-dungeons/9n8nj74fztg9",
     "img": "https://store-images.s-microsoft.com/image/apps.39985.14045794648370014.2229d39b-90c3-496e-8fac-9987450ca4d8.6db84bdb-2341-470a-88b0-0f119b204065",
     "blurb": "For Xbox Series X|S, Xbox One and Windows — also "
              "included with Xbox Game Pass, cloud play and all.",
     "tag": "Xbox · Windows · Game Pass", "go": "Xbox store",
     "w": 1920, "h": 1080},
    {"title": "Dungeons on Nintendo Switch",
     "url": "https://www.nintendo.com/us/store/products/minecraft-dungeons-switch/",
     "img": "https://www.minecraft.net/content/dam/minecraftnet/games/dungeons/key-art/MinecraftDungeons_Ultimate_Net_640x384.jpg",
     "blurb": "For Nintendo Switch: dungeon-crawling on the go, in "
              "TV, tabletop and handheld modes.",
     "tag": "Nintendo Switch", "go": "Nintendo store",
     "w": 640, "h": 384},
    {"title": "Dungeons on PlayStation",
     "url": "https://www.playstation.com/en-us/games/minecraft-dungeons/",
     "img": "https://image.api.playstation.com/gs2-sec/appkgo/prod/CUSA18779_00/4/i_c7b0467e8d83d7fa53d63d40a50e65e5da0edc39e07306e356cf5a6f2aba1977/i/icon0.png",
     "blurb": "For PS4 (playable on PS5): Sony's official Dungeons "
              "page, with the PlayStation Store editions.",
     "tag": "PlayStation · PS4", "go": "PlayStation",
     "w": 512, "h": 512},
]

# The ONE trailer: the official Minecraft channel's Dungeons
# Ultimate Edition trailer. YouTube oEmbed answered for this video
# on Oct 27, 2026 (author "Minecraft"), i.e. embedding is enabled;
# it ships as a click-to-play facade on the same pattern as
# /pop-haunt-culture — the player loads only on tap.
MINECRAFT_TRAILER = {"yt": "CoZ2V7XsSYk",
                     "title": "Minecraft Dungeons: Ultimate Edition "
                              "Trailer",
                     "img": "https://i.ytimg.com/vi/CoZ2V7XsSYk/hqdefault.jpg"}


# ------------------------------------------------- roblox shelf
# ROBLOX GAMES (Dan, Oct 27). Roblox blocks iframing, so every card
# is a LINK-OUT to the experience's official roblox.com page. All
# data verified Oct 27, 2026 from Roblox's OWN APIs (games.roblox.com
# details + apis.roblox.com omni-search, which returns each game's
# canonical URL and Roblox's official content-maturity label) — no
# fan wikis as the source of record. Art is each experience's own
# icon from Roblox's thumbnail CDN (tr.rbxcdn.com, curl-verified
# HTTP 200 with a gethauntmap.com Referer for every card).
#
# Curation: the platform's giants with a Halloween lean first.
# Maturity labels are Roblox's own, printed on every card. Murder
# Mystery 2 carries Roblox's "Moderate" label (cartoon whodunit
# violence) — shown plainly like the rest. The Mimic was checked
# specifically for its rating before inclusion: Roblox currently
# labels it Mild, the same class as DOORS and Piggy.
ROBLOX_GAMES = [
    {"title": "DOORS",
     "url": "https://www.roblox.com/games/6516141723/DOORS",
     "img": "https://tr.rbxcdn.com/180DAY-6d72472d3b2a47c5441194c8cf9f002c/512/512/Image/Png/noFilter",
     "blurb": "Roblox's haunted-hotel phenomenon: work through 100 "
              "doors, grab loot and outrun the entities hunting the "
              "halls — every death teaches you something. Loud sounds "
              "and flashing lights ahead!",
     "tag": "Adventure · Maturity: Mild", "byline": "by LSPLASH"},
    {"title": "The Mimic",
     "url": "https://www.roblox.com/games/6243699076/The-Mimic",
     "img": "https://tr.rbxcdn.com/180DAY-2035f6e350e78ced10a0b001dce70eae/512/512/Image/Png/noFilter",
     "blurb": "Four spooky storybooks drawn from Japanese history "
              "and urban legends: explore, solve and survive the "
              "things that mimic our world. Flashing lights, loud "
              "noises and jumpscares throughout.",
     "tag": "Horror · Maturity: Mild", "byline": "by CTStudio"},
    {"title": "Piggy",
     "url": "https://www.roblox.com/games/4623386862/Piggy",
     "img": "https://tr.rbxcdn.com/180DAY-027355d999aa09c6b486ad39dd8a48d2/512/512/Image/Png/noFilter",
     "blurb": "The survival-horror classic: solve the puzzles and "
              "escape the map before Piggy finds you — or be the "
              "Piggy and hunt your friends.",
     "tag": "Horror · Maturity: Mild",
     "byline": "by Piggy Dev Team"},
    {"title": "Rainbow Friends",
     "url": "https://www.roblox.com/games/7991339063/Rainbow-Friends",
     "img": "https://tr.rbxcdn.com/180DAY-52711cf678d6a095888b0d4c8f893809/512/512/Image/Png/noFilter",
     "blurb": "A field trip to the Odd World amusement park goes "
              "very wrong: survive nights of tasks while Blue, "
              "Green, Orange and Purple hunt you down.",
     "tag": "Horror · Maturity: Mild",
     "byline": "by Roy & Charcle"},
    {"title": "Murder Mystery 2",
     "url": "https://www.roblox.com/games/142823291/Murder-Mystery-2",
     "img": "https://tr.rbxcdn.com/180DAY-ab1484ff8063476d413da09dd25df93f/512/512/Image/Png/noFilter",
     "blurb": "The giant whodunit party game: Innocents run and "
              "hide, the Sheriff protects them, and one secret "
              "Murderer is on the loose. Collect and trade hundreds "
              "of knives.",
     "tag": "Horror · Maturity: Moderate", "byline": "by Nikilis"},
    {"title": "Brookhaven RP",
     "url": "https://www.roblox.com/games/4924922222/Brookhaven-RP",
     "img": "https://tr.rbxcdn.com/180DAY-577f3f78d1f056c80db7d2a54c8d384d/512/512/Image/Png/noFilter",
     "blurb": "Roblox's biggest hangout: claim a house, grab a car, "
              "pick a job and roleplay your own stories across a "
              "whole city — a Halloween candy-corn event is running "
              "right now.",
     "tag": "Town and City · Maturity: Minimal",
     "byline": "by Brookhaven by Voldex"},
    {"title": "Adopt Me!",
     "url": "https://www.roblox.com/games/920587237/Adopt-Me",
     "img": "https://tr.rbxcdn.com/180DAY-4dd71502e99ee8c47cbafec4c95c442d/512/512/Image/Png/noFilter",
     "blurb": "Raise pets, build your dream home and trade with "
              "friends in Roblox's beloved roleplay world — its "
              "Halloween event is on right now.",
     "tag": "RPG · Maturity: Minimal", "byline": "by Uplift Games"},
    {"title": "Tower of Hell",
     "url": "https://www.roblox.com/games/1962086868/Tower-of-Hell",
     "img": "https://tr.rbxcdn.com/180DAY-9704151d9c8a70e7ebe0ced8cb2b95c1/512/512/Image/Png/noFilter",
     "blurb": "The famous rage tower: race up a randomly built obby "
              "tower against the clock — no checkpoints, no mercy, "
              "endless bragging rights.",
     "tag": "Adventure · Maturity: Minimal",
     "byline": "by YXceptional Studios"},
    {"title": "Welcome to Bloxburg",
     "url": "https://www.roblox.com/games/185655149/Welcome-to-Bloxburg",
     "img": "https://tr.rbxcdn.com/180DAY-b6e76b3760f566e5b97b339609d72284/512/512/Image/Png/noFilter",
     "blurb": "Build and decorate the house of your dreams, work a "
              "job, level up your skills and live a whole second "
              "life in the town of Bloxburg.",
     "tag": "Town and City · Maturity: Minimal",
     "byline": "by Bloxburg Development"},
]


# ------------------------------------------------- iphone games shelf
# IPHONE GAMES (Dan, Oct 27, scope addition: "We'll find other games
# for the iPhone"). Every title below passed the SAME audit the
# iPhone Games Rule applies to the existing catalog (audit summary in
# the comment over PORTAL_GAMES):
#   * GamePix catalog feed: touch=true AND responsive=true;
#   * GamePix's own game page: JSON-LD availableOnDevice includes
#     "Mobile" and the Platform line lists Mobile;
#   * the vendor's own How-to-Play text documents a TOUCH path
#     (tap / touchscreen / finger / drag) -- metadata alone is NOT
#     enough (see the rejects);
#   * embed endpoint + cover art verified HTTP 200 on Oct 27, 2026.
# On iPhone this shelf LEADS /games (games.html moves it above the
# Halloween Arcade client-side); on desktop it joins the page as a
# normal shelf and changes nothing about the existing featuring.
#
# REJECTED at the same bar (do not add without re-verifying a touch
# path): moto-maniac-2 (vendor instructions are keyboard-only --
# arrows / WASD / P -- despite a Mobile device listing),
# boss-level-pumpkin-madness (movement is arrow keys + Z key),
# basketball-stars (keyboard controls, shared-keyboard 2-player).
# These rejects are the proof the audit bites: a Mobile flag in
# metadata does not earn a slot.
IPHONE_GAMES = [
    {"iphone": True, "slug": "bw-pumpkin",
     "img": "https://img.gamepix.com/games/bw-pumpkin/cover/bw-pumpkin.png?w=512",
     "title": "BW Pumpkin",
     "blurb": "A black-and-white endless jumper with a Halloween "
              "heart: tap to make the pumpkin leap the gaps -- "
              "higher, faster, longer, if your timing holds.",
     "tag": "Arcade jumper \u00b7 tap controls", "w": 480, "h": 320},
    {"iphone": True, "slug": "candy-bubble",
     "img": "https://img.gamepix.com/games/candy-bubble/cover/candy-bubble.png?w=512",
     "title": "Candy Bubble",
     "blurb": "A sweet spin on the classic bubble shooter: aim, "
              "fire and pop trios of candy bubbles to clear the board.",
     "tag": "Bubble shooter \u00b7 portrait play", "w": 320, "h": 480},
    {"iphone": True, "slug": "candy-monsters",
     "img": "https://img.gamepix.com/games/candy-monsters/cover/candy-monsters.png?w=512",
     "title": "Candy Monsters",
     "blurb": "Feed each little monster the candy in its own color -- "
              "and keep the wrong colors away from the wrong mouths.",
     "tag": "Arcade puzzle \u00b7 portrait play", "w": 320, "h": 480},
    {"iphone": True, "slug": "angry-monsters",
     "img": "https://img.gamepix.com/games/angry-monsters/cover/angry-monsters.png?w=512",
     "title": "Angry Monsters",
     "blurb": "Physics-fling monster mayhem: topple every tower and "
              "squash the critters across ten stages of careful chaos.",
     "tag": "Arcade physics", "w": 480, "h": 320},
    {"iphone": True, "slug": "candy-star-jelly-saga",
     "img": "https://img.gamepix.com/games/candy-star-jelly-saga/cover/candy-star-jelly-saga.png?w=512",
     "title": "Candy Star Jelly Saga",
     "blurb": "Match-3 candy swapping across 200+ levels of "
              "jelly-bright puzzles -- plan the swap, chase the combo.",
     "tag": "Match-3 puzzle \u00b7 portrait play", "w": 320, "h": 480},
    {"iphone": True, "slug": "candy-slingshot",
     "img": "https://img.gamepix.com/games/candy-slingshot/cover/candy-slingshot.png?w=512",
     "title": "Candy SlingShot",
     "blurb": "Tap, drag and let fly: slingshot candies into the "
              "targets, grab every star and dodge the hazards.",
     "tag": "Slingshot arcade \u00b7 portrait play", "w": 320, "h": 480},
    {"iphone": True, "slug": "block-puzzle-jewel",
     "img": "https://img.gamepix.com/games/block-puzzle-jewel/cover/block-puzzle-jewel.png?w=512",
     "title": "Block Puzzle Jewel",
     "blurb": "Fit the jewel blocks, complete the lines and keep "
              "the board from filling -- a calm, clever block puzzler.",
     "tag": "Block puzzle \u00b7 portrait play", "w": 320, "h": 480},
    {"iphone": True, "slug": "2048-x2-merge-blocks",
     "img": "https://img.gamepix.com/games/2048-x2-merge-blocks/cover/2048-x2-merge-blocks.png?w=512",
     "title": "2048 X2 Merge Blocks",
     "blurb": "2048 meets falling blocks: tap a column, drop the "
              "number and merge your way to bigger and bigger tiles.",
     "tag": "Merge puzzle \u00b7 portrait play", "w": 320, "h": 480},
    {"iphone": True, "slug": "bouncy-dunk",
     "img": "https://img.gamepix.com/games/bouncy-dunk/cover/bouncy-dunk.png?w=512",
     "title": "Bouncy Dunk",
     "blurb": "One tap launches the ball -- time the bounce, swish "
              "the moving hoop and keep the streak (and coins) coming.",
     "tag": "Arcade sports \u00b7 portrait play", "w": 320, "h": 480},
    {"iphone": True, "slug": "3d-darts",
     "img": "https://img.gamepix.com/games/3d-darts/cover/3d-darts.png?w=512",
     "title": "3D Darts",
     "blurb": "Tap to aim, release to throw: 3D darts duels with "
              "wind to read, opponents to beat and levels by the hundred.",
     "tag": "Sports \u00b7 portrait play", "w": 320, "h": 480},
    {"iphone": True, "slug": "babel-tower",
     "img": "https://img.gamepix.com/games/babel-tower/cover/babel-tower.png?w=512",
     "title": "Babel Tower",
     "blurb": "Build the Tower of Babel one tap at a time -- mine, "
              "craft and automate your crew's climb to the sky.",
     "tag": "Strategy builder", "w": 480, "h": 320},
    {"iphone": True, "slug": "a-mole-in-a-hole",
     "img": "https://img.gamepix.com/games/a-mole-in-a-hole/cover/a-mole-in-a-hole.png?w=512",
     "title": "A Mole in a Hole",
     "blurb": "Study the map, then dig the route from memory -- a "
              "forgetful mole needs your brain to get home for dinner.",
     "tag": "Memory puzzle \u00b7 portrait play", "w": 320, "h": 480},
]


@app.get("/games", response_class=HTMLResponse)
def games_page(request: Request):
    return templates.TemplateResponse(
        request, "games.html", {"portal_games": PORTAL_GAMES,
                                "ninjago_games": NINJAGO_GAMES,
                                "ninja_portal_games": NINJA_PORTAL_GAMES,
                                "ninja_link_games": NINJA_LINK_GAMES,
                                "minecraft_games": MINECRAFT_GAMES,
                                "minecraft_stores": MINECRAFT_DUNGEONS_STORES,
                                "minecraft_trailer": MINECRAFT_TRAILER,
                                "roblox_games": ROBLOX_GAMES,
                                "iphone_games": IPHONE_GAMES})


# ------------------------------------------------------------- ghost maze
# GHOST MAZE (Dan, Oct 25: "ours first, portal catalog later") — an
# original maze-chase arcade game built for HauntMap: our ghost, our
# maze, our monsters, all art drawn in code on a canvas. The genre's
# mechanics are free to use; nothing here reproduces any other game's
# name, maze, art, or audio. Engine: static/js/ghost_maze.js.
#
# Member leaderboard: game_scores holds ONE row per member — their
# best score — written only by the authenticated submit below.
# Anonymous players keep a device-local best (localStorage) and are
# nudged to join HauntSocial for the board.
#
# Plausibility cap, derived from the shipped maze (static/js/
# ghost_maze.js): 205 candy x 10 + 4 power pumpkins x 50 + chaser
# chains 4 x (200+400+800+1600) + 2 candy buckets x 1000 = 16,250
# points is a PERFECT level. 500,000 is ~30 perfect levels back to
# back — beyond any real run, so anything above it is not a score,
# it's a script.
GHOST_MAZE_SCORE_CAP = 500_000


def _ghost_maze_board(conn, limit: int = 10) -> list[dict]:
    rows = conn.execute(
        "SELECT u.handle, g.best_score, g.achieved_at FROM game_scores g "
        "JOIN users u ON u.id = g.user_id "
        "ORDER BY g.best_score DESC, g.achieved_at ASC LIMIT ?",
        (limit,)).fetchall()
    return [dict(r) for r in rows]


@app.get("/games/ghost-maze", response_class=HTMLResponse)
def ghost_maze_page(request: Request):
    member = getattr(request.state, "member", None)
    with get_conn(DB_PATH) as conn:
        board = _ghost_maze_board(conn)
        my_best = None
        if member:
            row = conn.execute(
                "SELECT best_score FROM game_scores WHERE user_id = ?",
                (member["id"],)).fetchone()
            my_best = row["best_score"] if row else None
    return templates.TemplateResponse(
        request, "ghost_maze.html",
        {"board": board, "my_best": my_best})


@app.post("/api/games/ghost-maze/score")
async def api_ghost_maze_score(request: Request):
    """Submit a finished GHOST MAZE run for the member leaderboard.

    Best-only: the stored row moves only when the new score beats it.
    Requires a member session (401 otherwise); the score must be a
    plain int inside [0, GHOST_MAZE_SCORE_CAP] or it's refused (422).
    Returns {ok, best, board} so the page can re-render its Top 10
    without a reload."""
    member = current_member(request)
    if member is None:
        return JSONResponse(
            {"error": "Sign in to save your score."}, status_code=401)
    try:
        data = await request.json()
    except Exception:
        data = {}
    score = data.get("score") if isinstance(data, dict) else None
    if isinstance(score, bool) or not isinstance(score, int) \
            or score < 0 or score > GHOST_MAZE_SCORE_CAP:
        return JSONResponse(
            {"error": "That score doesn't fit this maze."},
            status_code=422)
    now = datetime.now(timezone.utc).isoformat()
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT best_score FROM game_scores WHERE user_id = ?",
            (member["id"],)).fetchone()
        best = row["best_score"] if row else 0
        if score > best:
            conn.execute(
                "INSERT INTO game_scores (user_id, best_score, achieved_at) "
                "VALUES (?, ?, ?) ON CONFLICT(user_id) DO UPDATE SET "
                "best_score = excluded.best_score, "
                "achieved_at = excluded.achieved_at",
                (member["id"], score, now))
            conn.commit()
            best = score
        board = _ghost_maze_board(conn)
    return JSONResponse({"ok": True, "best": best, "board": board})


# ------------------------------------------------------------- daily trivia

TRIVIA_QUESTIONS = [
    {"q": "In what year was 'It's the Great Pumpkin, Charlie Brown' first aired on TV?", "options": ["1956", "1966", "1976", "1986"], "answer": 1},
    {"q": "Which horror film made Michael Myers famous?", "options": ["Friday the 13th", "A Nightmare on Elm Street", "Halloween", "Scream"], "answer": 2},
    {"q": "Before pumpkins, what vegetable did people in Ireland carve for Halloween?", "options": ["Potatoes", "Turnips", "Beets", "Onions"], "answer": 1},
    {"q": "What is a group of witches called?", "options": ["A flock", "A pack", "A coven", "A brood"], "answer": 2},
    {"q": "Which U.S. state grows the most pumpkins?", "options": ["Ohio", "Illinois", "California", "Pennsylvania"], "answer": 1},
    {"q": "What is the fear of Halloween called?", "options": ["Nyctophobia", "Samhainophobia", "Phasmophobia", "Wiccaphobia"], "answer": 1},
    {"q": "In 'Beetlejuice,' how many times do you say his name to summon him?", "options": ["Once", "Twice", "Three times", "Five times"], "answer": 2},
    {"q": "In the 1978 film 'Halloween,' what fictional town does Michael Myers terrorize?", "options": ["Elm Street", "Haddonfield", "Crystal Lake", "Sleepy Hollow"], "answer": 1},
    {"q": "What is the fear of spiders called?", "options": ["Arachnophobia", "Entomophobia", "Ophidiophobia", "Acrophobia"], "answer": 0},
    {"q": "From which region does Count Dracula hail?", "options": ["Bavaria", "Transylvania", "Bohemia", "Wallachia"], "answer": 1},
    {"q": "About how fast is the world record for carving a pumpkin?", "options": ["17 seconds", "45 seconds", "2 minutes", "5 minutes"], "answer": 0},
    {"q": "What was the medieval British tradition of going door to door for soul cakes called?", "options": ["Guising", "Mumming", "Souling", "Wassailing"], "answer": 2},
    {"q": "In 'The Addams Family,' what is the towering butler's name?", "options": ["Lurch", "Fester", "Gomez", "Thing"], "answer": 0},
    {"q": "Which famous escape artist died on Halloween in 1926?", "options": ["Harry Blackstone", "Howard Thurston", "Harry Houdini", "David Copperfield"], "answer": 2},
    {"q": "The Lewisburg Haunted Cave — one of the longest haunted attractions in the U.S. — is in which state?", "options": ["Pennsylvania", "Ohio", "Kentucky", "Indiana"], "answer": 1},
    {"q": "A teal pumpkin on a porch means the house offers what?", "options": ["Extra-large candy", "Allergy-friendly non-food treats", "A haunted walkthrough", "Free pumpkins"], "answer": 1},
    {"q": "Which film's villain asks, 'Do you want to play a game?'", "options": ["Saw", "It", "The Ring", "Insidious"], "answer": 0},
    {"q": "Which horror film is the highest-grossing of all time (not adjusted for inflation)?", "options": ["The Exorcist", "Jaws", "It (2017)", "Halloween (2018)"], "answer": 2},
    {"q": "Día de los Muertos (Day of the Dead) is primarily celebrated on which dates?", "options": ["Oct 30–31", "Oct 31–Nov 1", "Nov 1–2", "Nov 2–3"], "answer": 2},
    {"q": "In Irish folklore, the original jack-o'-lantern tale is about a man named…", "options": ["Wandering Willie", "Stingy Jack", "Black Tom", "Old Nick"], "answer": 1},
    {"q": "Which city hosts the famous Village Halloween Parade?", "options": ["Salem, MA", "New Orleans", "New York City", "Chicago"], "answer": 2},
    {"q": "What year was 'The Nightmare Before Christmas' released?", "options": ["1989", "1993", "1996", "2000"], "answer": 1},
    {"q": "What are the first names of the three Sanderson sisters in 'Hocus Pocus'?", "options": ["Winifred, Mary, Sarah", "Agatha, Mildred, Prudence", "Minnie, Daisy, Clara", "Elvira, Morticia, Lily"], "answer": 0},
    {"q": "Which classic Halloween candy was invented in the 1880s?", "options": ["Candy corn", "Tootsie Rolls", "Snickers", "Candy canes"], "answer": 0},
    {"q": "What creature supposedly has no reflection in a mirror?", "options": ["Werewolf", "Ghost", "Vampire", "Zombie"], "answer": 2},
    {"q": "October 30th — the night before Halloween — is traditionally known as what?", "options": ["Mischief Night", "Harvest Night", "Lantern Night", "Ghost Eve"], "answer": 0},
    {"q": "Which killer wears a hockey mask?", "options": ["Freddy Krueger", "Jason Voorhees", "Leatherface", "Ghostface"], "answer": 1},
    {"q": "What does Samhain, the ancient Celtic festival, mark?", "options": ["The spring planting", "The end of the harvest season", "The winter solstice", "The new year moon"], "answer": 1},
    {"q": "Which U.S. city calls itself the 'Halloween Capital of the World'?", "options": ["Salem, MA", "Anoka, MN", "Sleepy Hollow, NY", "New Orleans, LA"], "answer": 1},
    {"q": "In 'Monster Mash,' the narrator was working where when the monsters rose?", "options": ["In a graveyard", "In the lab", "At a castle ball", "In a haunted house"], "answer": 1},
]


def _trivia_quiz_for(day) -> list[dict]:
    """The 5-question quiz /trivia serves for one date — the page's
    existing selection logic, factored out unchanged (Item 6 needs the
    SAME selection so /daily can surface today's first question and
    have it match what /trivia asks). Selection is date-based: the
    date seeds a sample of 5 questions + a per-question option shuffle.
    NOTE the clock: /trivia has always seeded on the UTC date, so the
    quiz flips at UTC midnight (8pm ET in season), not ET midnight.
    That is the page's shipped behaviour; /daily mirrors it exactly
    rather than inventing a second, diverging "today", and Item 6's
    notes flag the ET-alignment as a separate deliberate change if
    Dan wants it."""
    rng = random.Random(day.toordinal())
    picks = rng.sample(TRIVIA_QUESTIONS, 5)
    quiz = []
    for i, item in enumerate(picks):
        order = list(range(4))
        random.Random(day.toordinal() * 10 + i).shuffle(order)
        quiz.append({
            "q": item["q"],
            "options": [item["options"][j] for j in order],
            "answer": order.index(item["answer"]),
        })
    return quiz


@app.get("/trivia", response_class=HTMLResponse)
def trivia_page(request: Request):
    today = datetime.now(timezone.utc).date()
    quiz = _trivia_quiz_for(today)
    return templates.TemplateResponse(
        request, "trivia.html", {"quiz": quiz, "today_label": today.strftime("%A, %B %-d")},
    )


# ------------------------------------------------------- Daily Fright (Wave 4, Item 6)

@app.get("/daily", response_class=HTMLResponse)
def daily_page(request: Request):
    """Daily Fright: ONE canonical drop per America/New_York date —
    (1) today's display (date-seeded deterministic pick from the
    Tonight's Display pool, _daily_display), (2) today's trivia
    question (the first question of the exact quiz /trivia serves
    today, via _trivia_quiz_for), (3) a Haunt or Not card into /games.
    Stable all day, rotates at ET midnight. The visit streak is
    JS/cookie-driven (hmFrightTouch in base.html) — visiting this page
    is one of the two counting surfaces; no server state is kept."""
    et_date = _today_et()
    with get_conn(DB_PATH) as conn:
        display = _daily_display(conn, et_date)
    quiz = _trivia_quiz_for(datetime.now(timezone.utc).date())
    date_label = et_date.strftime("%A, %B ") + str(et_date.day)
    return templates.TemplateResponse(
        request, "daily_fright.html",
        {"display": display,
         "trivia_q": quiz[0]["q"] if quiz else "",
         "date_label": date_label, "date_iso": et_date.isoformat()},
    )


@app.get("/api/duel")
def api_duel():
    exclude = sorted(DUEL_EXCLUDE_IDS)
    placeholders = ",".join("?" * len(exclude)) or "NULL"
    with get_conn(DB_PATH) as conn:
        conn.execute(DUEL_TABLE_SQL)
        rows = conn.execute(
            f"""SELECT e.*, COALESCE(s.wins, 0) AS dwins, COALESCE(s.battles, 0) AS dbattles
               FROM entries e LEFT JOIN duel_stats s ON s.entry_id = e.id
               WHERE e.category = 'halloween'
                 AND e.media_path IS NOT NULL AND e.media_path != ''
                 AND e.id NOT IN ({placeholders})
                 AND (e.tags IS NULL OR e.tags NOT LIKE '%2025%')
               ORDER BY dbattles ASC, RANDOM() LIMIT 80""",
            exclude,
        ).fetchall()
    pool = [row_to_dict(r) for r in rows]
    if len(pool) < 2:
        return JSONResponse({"error": "not enough haunts"}, status_code=503)
    a, b = random.sample(pool, 2)
    return {"a": _duel_slim(a), "b": _duel_slim(b)}


@app.post("/api/duel/vote")
async def api_duel_vote(request: Request):
    try:
        data = await request.json()
        winner, loser = int(data["winner"]), int(data["loser"])
    except Exception:
        return JSONResponse({"ok": False}, status_code=400)
    if winner == loser:
        return JSONResponse({"ok": False}, status_code=400)
    # The duel pool only ever serves 'halloween' entries (see api_duel);
    # refuse stats for anything else (venues included) so a crafted
    # POST can't put a non-haunt on the Haunt or Not board.
    with get_conn(DB_PATH) as conn:
        pair = {r["id"]: r for r in conn.execute(
            "SELECT id, category, hidden FROM entries WHERE id IN (?, ?)",
            (winner, loser)).fetchall()}
    if (len(pair) != 2
            or pair[winner]["category"] != "halloween"
            or pair[loser]["category"] != "halloween"
            or pair[winner]["hidden"] or pair[loser]["hidden"]):
        return JSONResponse({"ok": False}, status_code=400)
    with get_conn(DB_PATH) as conn:
        conn.execute(DUEL_TABLE_SQL)
        conn.execute(
            """INSERT INTO duel_stats (entry_id, wins, battles) VALUES (?, 1, 1)
               ON CONFLICT(entry_id) DO UPDATE SET wins = wins + 1, battles = battles + 1""",
            (winner,),
        )
        conn.execute(
            """INSERT INTO duel_stats (entry_id, wins, battles) VALUES (?, 0, 1)
               ON CONFLICT(entry_id) DO UPDATE SET battles = battles + 1""",
            (loser,),
        )
    return {"ok": True}


# ------------------------------------------------------------- haunt bracket
# Haunt Bracket: America's Scariest House (staged Oct 2026 — see
# app/bracket.py for seeds, round clock and rules). Voting reuses the
# duel pattern: JSON vote endpoint + cookie identity (the hm_voter
# cookie), one vote per matchup per browser, IP hash kept for audit.

def _bracket_teaser() -> dict:
    """Homepage module data (bracket band + Oct 31 champion treatment).
    Never allowed to break the homepage — any failure degrades to the
    plain pre-launch teaser."""
    try:
        now = brk.now_et()
        champ = None
        with get_conn(DB_PATH) as conn:
            conn.executescript(brk.TABLES_SQL)
            winners = brk.get_winners(conn)
        if "F" in winners:
            champ = get_entry(winners["F"])
        label, when = brk.next_milestone(now)
        return {"phase": brk.phase(now), "champion": champ,
                "milestone_label": label, "milestone_at": when,
                "crown_at": brk.CROWN_AT}
    except Exception:
        return {"phase": "pre", "champion": None,
                "milestone_label": "Voting opens — Round of 16",
                "milestone_at": brk.ROUNDS[0]["opens"], "crown_at": brk.CROWN_AT}


def _bracket_entries() -> dict[int, dict]:
    out: dict[int, dict] = {}
    for seed, entry_id in brk.SEEDS.items():
        e = get_entry(entry_id)
        if not e:
            continue
        e = dict(e)
        e["seed"] = seed
        e["region"] = brk.REGIONS.get(entry_id, "")
        e["has_video"] = entry_id in brk.HAS_VIDEO
        e["seed_note"] = brk.SEED_NOTES.get(entry_id, "")
        out[entry_id] = e
    return out


def _bracket_state(request: Request) -> dict:
    now = brk.now_et()
    entries = _bracket_entries()
    voter = request.cookies.get("hm_voter", "")
    with get_conn(DB_PATH) as conn:
        conn.executescript(brk.TABLES_SQL)
        winners = brk.get_winners(conn)
        counts = {m: brk.vote_counts(conn, m) for m in brk.ALL_MATCHUPS}
        my_votes: dict[str, int] = {}
        my_prediction = None
        if voter:
            my_votes = {r["matchup_id"]: r["entry_id"] for r in conn.execute(
                "SELECT matchup_id, entry_id FROM bracket_votes WHERE voter = ?",
                (voter,)).fetchall()}
            prow = conn.execute(
                "SELECT * FROM bracket_predictions WHERE voter = ?",
                (voter,)).fetchone()
            if prow:
                my_prediction = dict(prow)
                my_prediction["picks"] = json.loads(my_prediction["picks"])
                my_prediction["score"] = brk.prediction_score(
                    my_prediction["picks"], winners)
        board = []
        for r in conn.execute(
                "SELECT handle, picks FROM bracket_predictions").fetchall():
            picks = json.loads(r["picks"])
            board.append({
                "handle": r["handle"],
                "score": brk.prediction_score(picks, winners),
                "champ": picks.get("F"),
                "champ_alive": ("F" not in winners
                                or picks.get("F") == winners.get("F")),
            })
        board.sort(key=lambda b: (-b["score"], b["handle"].lower()))
        total_votes = sum(sum(c.values()) for c in counts.values())
    rounds_out = []
    for rnd in brk.ROUNDS:
        status = ("open" if rnd["opens"] <= now <= rnd["closes"]
                  else "upcoming" if now < rnd["opens"] else "closed")
        ms = []
        for mid in rnd["matchups"]:
            a_id, b_id = brk.matchup_pair(mid, winners)
            c = counts.get(mid, {})
            total = sum(c.values())
            def side(eid):
                if eid is None:
                    return None
                e = dict(entries.get(eid, {}))
                e["votes"] = c.get(eid, 0)
                e["pct"] = round(100 * c.get(eid, 0) / total) if total else 0
                return e
            feeders = brk.FEEDS.get(mid)
            ms.append({
                "id": mid, "a": side(a_id), "b": side(b_id),
                "a_label": (entries.get(a_id, {}).get("title") if a_id else
                            (f"Winner of {feeders[0]}" if feeders else "TBD")),
                "b_label": (entries.get(b_id, {}).get("title") if b_id else
                            (f"Winner of {feeders[1]}" if feeders else "TBD")),
                "total": total, "winner": winners.get(mid),
                "my_vote": my_votes.get(mid), "status": status,
            })
        rounds_out.append({
            "key": rnd["key"], "label": brk.ROUND_LABELS[rnd["key"]],
            "opens": rnd["opens"], "closes": rnd["closes"],
            "status": status, "matchups": ms,
            "window_label": (rnd["opens"].strftime("%a %b %-d") + " – "
                             + rnd["closes"].strftime("%a %b %-d")),
        })
    label, when = brk.next_milestone(now)
    champion = None
    if "F" in winners:
        champion = entries.get(winners["F"])
    return {
        "now": now, "phase": brk.phase(now), "rounds": rounds_out,
        "entries": entries, "winners": winners, "my_votes": my_votes,
        "my_prediction": my_prediction, "board": board[:25],
        "board_total": len(board), "total_votes": total_votes,
        "milestone_label": label, "milestone_at": when,
        "predict_open": now <= brk.PREDICT_LOCK,
        "predict_lock": brk.PREDICT_LOCK, "champion": champion,
        "crown_at": brk.CROWN_AT, "is_admin": is_admin(request),
    }


@app.get("/bracket", response_class=HTMLResponse)
def bracket_page(request: Request):
    st = _bracket_state(request)
    seeds_sorted = sorted(st["entries"].values(), key=lambda e: e["seed"])
    return templates.TemplateResponse(request, "bracket.html", {
        "request": request, "st": st, "seeds": seeds_sorted,
        "predicted": request.query_params.get("predicted") == "1",
        "predict_locked_msg": request.query_params.get("predict") == "locked",
    })


@app.post("/api/bracket/vote")
async def api_bracket_vote(request: Request):
    try:
        data = await request.json()
        matchup_id, entry_id = str(data["matchup"]), int(data["entry"])
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"}, status_code=400)
    now = brk.now_et()
    rnd = next((r for r in brk.ROUNDS if r["key"] == brk.ROUND_OF.get(matchup_id)), None)
    if rnd is None or not (rnd["opens"] <= now <= rnd["closes"] + timedelta(minutes=1)):
        return JSONResponse({"ok": False, "error": "voting is not open for this matchup"},
                            status_code=403)
    voter = request.cookies.get("hm_voter", "")
    new_cookie = None
    if not voter:
        voter = uuid.uuid4().hex
        new_cookie = voter
    with get_conn(DB_PATH) as conn:
        conn.executescript(brk.TABLES_SQL)
        winners = brk.get_winners(conn)
        a_id, b_id = brk.matchup_pair(matchup_id, winners)
        if entry_id not in (a_id, b_id):
            return JSONResponse({"ok": False, "error": "not a matchup entry"},
                                status_code=400)
        conn.execute(
            "INSERT OR IGNORE INTO bracket_votes (matchup_id, entry_id, voter, ip_hash, created_at) "
            "VALUES (?, ?, ?, ?, ?)",
            (matchup_id, entry_id, voter, brk.ip_hash(request),
             datetime.now(timezone.utc).isoformat()))
        conn.commit()
        counts = brk.vote_counts(conn, matchup_id)
    total = sum(counts.values())
    resp = JSONResponse({"ok": True, "matchup": matchup_id, "total": total,
                         "counts": {str(k): v for k, v in counts.items()},
                         "pct": {str(k): (round(100 * v / total) if total else 0)
                                 for k, v in counts.items()}})
    if new_cookie:
        resp.set_cookie("hm_voter", new_cookie, max_age=365 * 24 * 3600,
                        path="/", samesite="lax")
    return resp


@app.get("/api/bracket/state")
def api_bracket_state(request: Request):
    st = _bracket_state(request)
    out = {"phase": st["phase"], "total_votes": st["total_votes"], "matchups": {}}
    for rnd in st["rounds"]:
        for m in rnd["matchups"]:
            out["matchups"][m["id"]] = {
                "total": m["total"], "winner": m["winner"],
                "a_votes": m["a"]["votes"] if m["a"] else 0,
                "b_votes": m["b"]["votes"] if m["b"] else 0,
                "a_pct": m["a"]["pct"] if m["a"] else 0,
                "b_pct": m["b"]["pct"] if m["b"] else 0,
                "my_vote": m["my_vote"],
            }
    return out


@app.post("/bracket/predict")
async def bracket_predict(request: Request):
    now = brk.now_et()
    if now > brk.PREDICT_LOCK:
        return RedirectResponse("/bracket?predict=locked#predictions", status_code=303)
    form = await request.form()
    handle = re.sub(r"<[^>]*>", "", str(form.get("handle", ""))).strip()[:24]
    contact = str(form.get("contact", "")).strip()[:120]
    if not handle:
        return RedirectResponse("/bracket#predictions", status_code=303)
    picks: dict[str, int] = {}
    ok = True
    with get_conn(DB_PATH) as conn:
        winners = brk.get_winners(conn)
    for mid in brk.ALL_MATCHUPS:
        raw = str(form.get(f"pick_{mid}", "")).strip()
        if not raw.isdigit():
            ok = False
            break
        picks[mid] = int(raw)
    if ok:  # cascade consistency: later-round picks must come from your own
        for mid, (f1, f2) in brk.FEEDS.items():  # feeding picks
            if picks[mid] not in (picks[f1], picks[f2]):
                ok = False
                break
    if not ok:
        return RedirectResponse("/bracket#predictions", status_code=303)
    voter = request.cookies.get("hm_voter", "")
    new_cookie = None
    if not voter:
        voter = uuid.uuid4().hex
        new_cookie = voter
    ts = datetime.now(timezone.utc).isoformat()
    with get_conn(DB_PATH) as conn:
        conn.executescript(brk.TABLES_SQL)
        conn.execute(
            "INSERT INTO bracket_predictions (voter, handle, contact, picks, created_at, updated_at) "
            "VALUES (?, ?, ?, ?, ?, ?) ON CONFLICT(voter) DO UPDATE SET "
            "handle = excluded.handle, contact = excluded.contact, "
            "picks = excluded.picks, updated_at = excluded.updated_at",
            (voter, handle, contact, json.dumps(picks), ts, ts))
        conn.commit()
    resp = RedirectResponse("/bracket?predicted=1#predictions", status_code=303)
    if new_cookie:
        resp.set_cookie("hm_voter", new_cookie, max_age=365 * 24 * 3600,
                        path="/", samesite="lax")
    return resp


@app.post("/admin/bracket/resolve/{matchup_id}")
def bracket_resolve(request: Request, matchup_id: str):
    if not is_admin(request):
        raise HTTPException(403, "Admin only.")
    if matchup_id not in brk.ALL_MATCHUPS:
        raise HTTPException(404, "No such matchup.")
    with get_conn(DB_PATH) as conn:
        winner = brk.resolve_matchup(conn, matchup_id)
    if winner is None:
        raise HTTPException(409, "Feeders unresolved.")
    return RedirectResponse("/bracket", status_code=303)


@app.get("/bracket/card/{entry_id}", response_class=HTMLResponse)
def bracket_card(request: Request, entry_id: int):
    if entry_id not in brk.SEED_OF:
        raise HTTPException(404, "Not a bracket contender.")
    e = get_entry(entry_id)
    if not e:
        raise HTTPException(404, "Entry not found.")
    e = dict(e)
    e["seed"] = brk.SEED_OF[entry_id]
    e["region"] = brk.REGIONS.get(entry_id, "")
    return templates.TemplateResponse(request, "bracket_card.html",
                                        {"request": request, "e": e})


@app.get("/watch", response_class=HTMLResponse)
def watch_page(request: Request):
    """Vertical feed of every pin with actual footage — same predicate as the
    feed's 'Has video' filter: a TikTok /video/ URL or an uploaded video file.

    Retention Wave 2, Items 2 + 7 (Dan, Oct 23): /watch is the TikTok
    landing page, so it follows the site's location-first rule. The
    server pool follows Dan's Oct 23 feed-order rule: Dan's
    hand-picked footage pins first (newest hand-picked first), then
    the newest footage pins, capped at 60 — that server order is also
    the final order when the visitor's town is unknown. (This
    supersedes the earlier most-viewed pool.) When the visitor's town IS known
    (localStorage 'hm_town' — the server never sees it), watch.html
    re-orders client-side from the payload below: most-viewed footage
    within VIDEO_CHAIN_RADIUS_MI of the visitor first, nearest to the
    visitor breaking ties, the rest in server order behind — the same
    anchoring detail_chain's video chain uses. This supersedes the
    Oct 21 per-visit shuffle. Every slide also carries _views for
    Item 7's count chips (from the cached views snapshot)."""
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT e.* FROM entries e "
            "WHERE e.hidden = 0 AND ("
            "(e.tiktok_url IS NOT NULL AND e.tiktok_url LIKE '%/video/%')"
            " OR LOWER(e.media_path) LIKE '%.mp4'"
            " OR LOWER(e.media_path) LIKE '%.webm'"
            " OR LOWER(e.media_path) LIKE '%.mov')"
            " ORDER BY e.is_handpicked DESC, e.created_at DESC, e.id DESC "
            "LIMIT 60").fetchall()
    # _views from the TTL-cached views snapshot (fortification pass 2)
    # instead of a per-render page_views GROUP BY join.
    views = _views_by_id()
    entries = []
    for r in rows:
        d = row_to_dict(r)
        d["_views"] = views.get(d["id"], 0)
        entries.append(d)
    # Town centers for the client-side visitor anchoring, in the same
    # [label, city, state, centroid lat, centroid lng, pin count]
    # shape detail.html's video-chain re-pick consumes — computed from
    # this pool's own pins (every category /watch carries, not just
    # halloween), so the resolver's town universe matches the feed.
    _groups: dict[str, dict] = {}
    for e in entries:
        if e.get("lat") is None or e.get("lng") is None or not e["town_label"]:
            continue
        g = _groups.setdefault(e["town_label"],
                               {"_lats": [], "_lngs": [], "count": 0})
        g["_lats"].append(e["lat"])
        g["_lngs"].append(e["lng"])
        g["count"] += 1
    town_centers = [
        [label, extract_city(label), extract_state(label),
         sum(g["_lats"]) / len(g["_lats"]), sum(g["_lngs"]) / len(g["_lngs"]),
         g["count"]]
        for label, g in sorted(_groups.items())]
    return templates.TemplateResponse(request, "watch.html",
        {"request": request, "entries": entries,
         "town_centers": town_centers})


# ---------------------------------------------------------------- virtual tour

VT_ROUTE_LEN = 12

# Long Island channel (Dan, Oct 27): the Nassau + Suffolk towns that
# actually carry video pins in the pool, matched on the parsed city so
# address-form town strings ('417 S 1st St, Lindenhurst, NY') count too.
# Membership is NOT exclusive — these stops stay in NYC Metro as well.
VT_LI_CITIES = {
    "Bethpage", "Deer Park", "East Islip", "Levittown", "Lindenhurst",
    "Melville", "Merrick", "Old Bethpage", "Plainview", "West Islip",
}


def _vt_video_pool(conn) -> list[dict]:
    """Playable-video pins eligible for a Virtual Tour: a TikTok /video/
    URL or an uploaded video file, with a thumbnail and map coordinates,
    never 2025-tagged (the same currency rule as Tonight's Display). Each
    dict carries _views (detail-page views) as the popularity signal —
    votes are near-zero on video pins, views are what actually rank them.
    A display listed twice (same title + town) appears once."""
    rows = conn.execute(
        """SELECT e.* FROM entries e
           WHERE e.hidden = 0
             AND ((e.tiktok_url IS NOT NULL AND e.tiktok_url LIKE '%/video/%')
                  OR LOWER(e.media_path) LIKE '%.mp4'
                  OR LOWER(e.media_path) LIKE '%.webm'
                  OR LOWER(e.media_path) LIKE '%.mov')
             AND e.thumb_path IS NOT NULL AND TRIM(e.thumb_path) != ''
             AND e.lat IS NOT NULL AND e.lng IS NOT NULL
             AND NOT (',' || COALESCE(e.tags, '') || ',') LIKE '%,2025,%'
           ORDER BY e.id""").fetchall()
    # _views from the TTL-cached views snapshot (fortification pass 2)
    # instead of a per-render page_views GROUP BY join.
    views = _views_by_id(conn)
    out, seen_keys = [], set()
    for r in rows:
        d = row_to_dict(r)
        d["_views"] = views.get(d["id"], 0)
        key = ((d.get("title") or "").strip().lower(), d["town_label"])
        if key in seen_keys:
            continue
        seen_keys.add(key)
        d["_state"] = extract_state(d.get("town") or "")
        d["_kind"] = ("tiktok" if "/video/" in (d.get("tiktok_url") or "")
                      else "video")
        out.append(d)
    return out


def _vt_kind(d: dict) -> str:
    """Stop kind for the tour player: a TikTok embed, an uploaded video,
    or a photo (states the video supply hasn't reached yet)."""
    if "/video/" in (d.get("tiktok_url") or ""):
        return "tiktok"
    mp = (d.get("media_path") or "").lower()
    if mp.endswith((".mp4", ".webm", ".mov")):
        return "video"
    return "photo"


def _vt_photo_pool(conn, exclude_ids: set) -> list[dict]:
    """Photo stops: live pins with a real uploaded photo + thumbnail and
    map coordinates, never 2025-tagged — the same currency/media rules
    as the video pool. These represent states the video pool can't
    reach yet on the All America route (video first, strongest photo
    where a state has no video)."""
    rows = conn.execute(
        """SELECT e.* FROM entries e
           WHERE e.hidden = 0
             AND e.lat IS NOT NULL AND e.lng IS NOT NULL
             AND e.thumb_path IS NOT NULL AND TRIM(e.thumb_path) != ''
             AND e.media_path IS NOT NULL AND TRIM(e.media_path) != ''
             AND LOWER(e.media_path) NOT LIKE '%.mp4'
             AND LOWER(e.media_path) NOT LIKE '%.webm'
             AND LOWER(e.media_path) NOT LIKE '%.mov'
             AND NOT (e.tiktok_url IS NOT NULL
                      AND e.tiktok_url LIKE '%/video/%')
             AND NOT (',' || COALESCE(e.tags, '') || ',') LIKE '%,2025,%'
           ORDER BY e.id""").fetchall()
    views = _views_by_id(conn)
    out, seen_keys = [], set()
    for r in rows:
        d = row_to_dict(r)
        if d["id"] in exclude_ids:
            continue
        d["_views"] = views.get(d["id"], 0)
        key = ((d.get("title") or "").strip().lower(), d["town_label"])
        if key in seen_keys:
            continue
        seen_keys.add(key)
        d["_state"] = extract_state(d.get("town") or "")
        d["_kind"] = "photo"
        out.append(d)
    return out


# All 50 states + DC: names, a fitting little emoji per state (the
# curated channels set the pattern — 🐊 FL, 🤠 TX, 🌵 AZ), and a
# west→east sweep order so the All America ride crosses the country
# instead of teleporting around it.
VT_STATE_NAMES = {
    "AL": "Alabama", "AK": "Alaska", "AZ": "Arizona", "AR": "Arkansas",
    "CA": "California", "CO": "Colorado", "CT": "Connecticut",
    "DE": "Delaware", "DC": "Washington DC", "FL": "Florida",
    "GA": "Georgia", "HI": "Hawaii", "ID": "Idaho", "IL": "Illinois",
    "IN": "Indiana", "IA": "Iowa", "KS": "Kansas", "KY": "Kentucky",
    "LA": "Louisiana", "ME": "Maine", "MD": "Maryland",
    "MA": "Massachusetts", "MI": "Michigan", "MN": "Minnesota",
    "MS": "Mississippi", "MO": "Missouri", "MT": "Montana",
    "NE": "Nebraska", "NV": "Nevada", "NH": "New Hampshire",
    "NJ": "New Jersey", "NM": "New Mexico", "NY": "New York",
    "NC": "North Carolina", "ND": "North Dakota", "OH": "Ohio",
    "OK": "Oklahoma", "OR": "Oregon", "PA": "Pennsylvania",
    "RI": "Rhode Island", "SC": "South Carolina", "SD": "South Dakota",
    "TN": "Tennessee", "TX": "Texas", "UT": "Utah", "VT": "Vermont",
    "VA": "Virginia", "WA": "Washington", "WV": "West Virginia",
    "WI": "Wisconsin", "WY": "Wyoming",
}
VT_STATE_EMOJI = {
    "AL": "🎶", "AK": "🐻", "AZ": "🌵", "AR": "💎", "CA": "🌴",
    "CO": "🏔️", "CT": "⚓", "DE": "🏖️", "DC": "🏛️", "FL": "🐊",
    "GA": "🍑", "HI": "🌺", "ID": "🥔", "IL": "🌆", "IN": "🏁",
    "IA": "🌽", "KS": "🌻", "KY": "🐎", "LA": "🎷", "ME": "🦞",
    "MD": "🦀", "MA": "🦃", "MI": "🚗", "MN": "🛶", "MS": "🎸",
    "MO": "🎵", "MT": "🦬", "NE": "🌾", "NV": "🎰", "NH": "🍁",
    "NJ": "🎃", "NM": "🌶️", "NY": "🗽", "NC": "🛩️", "ND": "🦌",
    "OH": "🚀", "OK": "🌪️", "OR": "🌲", "PA": "🔔", "RI": "⛵",
    "SC": "🌙", "SD": "🗿", "TN": "🎻", "TX": "🤠", "UT": "🏜️",
    "VT": "🍦", "VA": "🌊", "WA": "☕", "WV": "⛰️", "WI": "🧀",
    "WY": "♨️",
}
VT_STATE_ORDER = [
    "WA", "OR", "CA", "NV", "ID", "UT", "AZ", "MT", "WY", "CO", "NM",
    "ND", "SD", "NE", "KS", "OK", "TX", "MN", "IA", "MO", "AR", "LA",
    "WI", "IL", "MS", "MI", "IN", "KY", "TN", "AL", "OH", "GA", "FL",
    "SC", "NC", "VA", "WV", "DC", "MD", "DE", "PA", "NY", "NJ", "CT",
    "RI", "MA", "VT", "NH", "ME", "AK", "HI",
]
VT_AMERICA_LEN = 64


def _vt_america(pool: list[dict], photo_pool: list[dict]) -> list[dict]:
    """All America route (Dan, Oct 26 — 'the whole country
    represented'): one guaranteed stop per state + DC that has pins,
    then a second VIDEO stop for states that have one to spare.
    Within a state, video pins rank ahead of photo pins, then views —
    video first, strongest photo where a state has no video yet.
    Stops ride in a west→east state sweep, rep first in each state."""
    def rank(d):
        return (0 if d["_kind"] != "photo" else 1,
                -d["_views"], -d["votes"], d["id"])

    by_state: dict[str, list[dict]] = {}
    for d in list(pool) + list(photo_pool):
        st = d["_state"]
        if st not in VT_STATE_NAMES:  # US states + DC only
            continue
        by_state.setdefault(st, []).append(d)
    order = {st: i for i, st in enumerate(VT_STATE_ORDER)}
    picked = []  # (state sweep idx, is-extra, -views, stop)
    for st, lst in by_state.items():
        lst.sort(key=rank)
        picked.append((order.get(st, 99), 0, -lst[0]["_views"], lst[0]))
        for d in lst[1:]:
            if d["_kind"] != "photo":
                picked.append((order.get(st, 99), 1, -d["_views"], d))
                break
    picked.sort(key=lambda t: t[:3])
    return [t[3] for t in picked[:VT_AMERICA_LEN]]


def _vt_pick(pool: list[dict], key, n: int = VT_ROUTE_LEN,
             town_cap: int = 2) -> list[dict]:
    """Greedy route pick: rank by key, cap stops per town so one town can't
    eat the route (geographic variety), then backfill past the cap if the
    pool runs short."""
    ranked = sorted(pool, key=key)
    picked, counts = [], {}
    for d in ranked:
        if len(picked) >= n:
            break
        t = d["town_label"]
        if counts.get(t, 0) >= town_cap:
            continue
        counts[t] = counts.get(t, 0) + 1
        picked.append(d)
    if len(picked) < n:
        have = {d["id"] for d in picked}
        for d in ranked:
            if len(picked) >= n:
                break
            if d["id"] not in have:
                picked.append(d)
    return picked


@app.get("/virtual-tour", response_class=HTMLResponse)
def virtual_tour_page(request: Request, route: str = "tonight",
                      mode: str = ""):
    """Virtual Tour (Dan, Oct 23 — STAGED for preview): a lean-back guided
    run through the best video haunts on the map, presented as one tour.
    Routes are rebuilt from live data on every load, so the 'nightly
    rebuild' is automatic — no cron: Tonight's Tour ranks the whole video
    pool by detail-page views; Scariest in America ranks the creepy+
    pool by scare level, then views. Both cap at 2 stops per town.

    HauntMap TV (Dan, Oct 23, scope extension — same staged branch):
    mode=tv renders the same player machinery as a lean-back TV surface
    with a channel picker. Channels are Tonight's Tour + Scariest plus
    the two state/metro playlists the video supply actually supports —
    NYC Metro (every video pin in the pool is downstate NY: the five
    boroughs + Long Island) and New Jersey — each ranked by views with
    the same 2-per-town cap. A channel thinner than 6 stops is hidden,
    exactly like the Scariest tab rule.

    Oct 26 expansion (STAGED for Dan's approval): the pool has since
    grown far beyond downstate NY, so the same mechanism now also feeds
    a Family Friendly route plus the state/metro clusters the supply
    supports — Virginia, Florida, Chicagoland, Texas, Colorado, Arizona,
    Las Vegas, and California split into Bay Area vs Southern California.
    Salem MA / New Orleans / Hudson Valley have no video pins in the
    pool yet, so they can't carry a route; Bergen County already rides
    inside the NJ route. Long Island rode inside NYC Metro until
    Oct 27, when Dan gave it a channel of its own — its stops stay in
    NYC Metro too (channel membership is not exclusive).

    Whole-country expansion (Dan, Oct 26 — 'add as many states as
    possible, the whole country represented in Haunt TV and virtual
    tour'): an All America channel guarantees one stop per state + DC
    that has pins — the state's best video pin, or its strongest photo
    pin where the state has no video yet (photo stops dwell and roll
    on, in both the tour ride and TV mode) — plus a second video stop
    per state that has one. And the state channels are now systematic:
    any state whose video pool reaches the 6-stop gate gets a channel
    automatically, no hand-list to extend."""
    with get_conn(DB_PATH) as conn:
        pool = _vt_video_pool(conn)
        photo_pool = _vt_photo_pool(conn, {d["id"] for d in pool})
    by_views = lambda d: (-d["_views"], -d["votes"], d["id"])  # noqa: E731
    tonight = _vt_pick(pool, key=by_views)
    scare_rank = {"extreme": 0, "terrifying": 1, "creepy": 2}
    scary_pool = [d for d in pool if d.get("scare_level") in scare_rank]
    scariest = _vt_pick(
        scary_pool,
        key=lambda d: (scare_rank[d["scare_level"]], -d["_views"],
                       -d["votes"], d["id"]))
    nyc = _vt_pick([d for d in pool if d["_state"] == "NY"], key=by_views)
    # Long Island gets its own channel (Dan, Oct 27): the Nassau +
    # Suffolk slice of the NY pool. Non-exclusive — the same stops
    # stay in NYC Metro above.
    li = _vt_pick([d for d in pool if d["_state"] == "NY"
                   and extract_city(d["town"]) in VT_LI_CITIES],
                  key=by_views)
    nj = _vt_pick([d for d in pool if d["_state"] == "NJ"], key=by_views)
    # More prebuilt tours (Dan, Oct 26 — STAGED for his approval): the same
    # mechanism on the clusters the video pool actually supports — a
    # family-rated counterpart to Scariest, then state/metro picks ranked
    # by views with the same 2-per-town cap and the same >=6 gate. The CA
    # pool splits at 36.9N / 121.5W: Bay Area (SF + San Jose + Peninsula)
    # vs SoCal (LA + Orange County); Sacramento-area / Central Valley pins
    # sit in neither and stay in the national routes.
    family = _vt_pick(
        [d for d in pool if (d.get("scare_level") or "") == "family"],
        key=by_views)
    virginia = _vt_pick([d for d in pool if d["_state"] == "VA"], key=by_views)
    florida = _vt_pick([d for d in pool if d["_state"] == "FL"], key=by_views)
    chicagoland = _vt_pick([d for d in pool if d["_state"] == "IL"],
                           key=by_views)
    texas = _vt_pick([d for d in pool if d["_state"] == "TX"], key=by_views)
    colorado = _vt_pick([d for d in pool if d["_state"] == "CO"], key=by_views)
    arizona = _vt_pick([d for d in pool if d["_state"] == "AZ"], key=by_views)
    vegas = _vt_pick([d for d in pool if d["_state"] == "NV"], key=by_views)
    bayarea = _vt_pick(
        [d for d in pool if d["_state"] == "CA"
         and d["lat"] >= 36.9 and d["lng"] <= -121.5], key=by_views)
    socal = _vt_pick(
        [d for d in pool if d["_state"] == "CA" and d["lat"] < 36.9],
        key=by_views)
    america = _vt_america(pool, photo_pool)
    # Systematic state channels: the curated routes above cover NY,
    # NJ, VA, FL, IL, TX, CO, AZ, NV and CA (split in two). Any OTHER
    # state whose video supply reaches the same >=6 gate earns its own
    # channel automatically, so coverage survives new content with no
    # hand-list to maintain.
    _covered_states = {"NY", "NJ", "VA", "FL", "IL", "TX", "CO", "AZ",
                       "NV", "CA"}
    state_routes = {}
    for st in sorted({d["_state"] for d in pool}):
        if st in _covered_states or st not in VT_STATE_NAMES:
            continue
        stops = _vt_pick([d for d in pool if d["_state"] == st],
                         key=by_views)
        if len(stops) >= 6:
            state_routes[st] = stops
    routes = {"tonight": tonight}
    if len(scariest) >= 6:  # thinner than that isn't a tour — hide the tab
        routes["scariest"] = scariest
    if len(family) >= 6:
        routes["family"] = family
    if len(nyc) >= 6:
        routes["nyc"] = nyc
    if len(li) >= 6:
        routes["li"] = li
    if len(nj) >= 6:
        routes["nj"] = nj
    if len(virginia) >= 6:
        routes["virginia"] = virginia
    if len(florida) >= 6:
        routes["florida"] = florida
    if len(chicagoland) >= 6:
        routes["chicagoland"] = chicagoland
    if len(texas) >= 6:
        routes["texas"] = texas
    if len(colorado) >= 6:
        routes["colorado"] = colorado
    if len(arizona) >= 6:
        routes["arizona"] = arizona
    if len(vegas) >= 6:
        routes["vegas"] = vegas
    if len(bayarea) >= 6:
        routes["bayarea"] = bayarea
    if len(socal) >= 6:
        routes["socal"] = socal
    if len(america) >= 6:
        routes["america"] = america
    for st, stops in state_routes.items():
        routes[f"state-{st.lower()}"] = stops
    if route not in routes:
        route = "tonight"
    is_tv = mode == "tv"
    channel_meta = [
        {"id": "tonight", "label": "Tonight's Tour", "emoji": "🎬",
         "featured": True,
         "title": "🎬 Tonight's Virtual Tour",
         "sub": "The best video haunts in the country, one after another "
                "— sit back and ride along.",
         "blurb": "Tonight's best video haunts nationwide, ranked by "
                  "what haunters are actually watching."},
        {"id": "scariest", "label": "Scariest in America", "emoji": "😱",
         "featured": True,
         "title": "😱 Scariest in America — Virtual Tour",
         "sub": "The most terrifying video haunts on the map, ranked by "
                "scare level — enter if you dare.",
         "blurb": "The creepiest, most terrifying video haunts on the "
                  "map, ranked by scare level."},
        {"id": "america", "label": "All America", "emoji": "🗺️",
         "featured": True, "unit": "haunts — videos & photos",
         "title": "🗺️ All America — Coast to Coast Virtual Tour",
         "sub": "Every state on the map, one stop at a time — each "
                "state's best video haunt, and its strongest photo "
                "where video hasn't reached yet.",
         "blurb": "Coast to coast: a stop in every state + DC on the "
                  "map — video first, a photo stop where a state has "
                  "no video yet."},
        {"id": "nyc", "label": "NYC Metro", "emoji": "🗽",
         "title": "🗽 NYC Metro — Virtual Tour",
         "sub": "Video haunts across the five boroughs and Long Island "
                "— the densest haunting in America, one stop at a time.",
         "blurb": "The five boroughs + Long Island: Dyker Heights, "
                  "Staten Island, Lindenhurst and more."},
        {"id": "li", "label": "Long Island", "emoji": "👻",
         "title": "👻 Long Island — Virtual Tour",
         "sub": "Nassau and Suffolk's best video haunts — Lindenhurst, "
                "Plainview, Levittown and more, ranked by views.",
         "blurb": "Lindenhurst, Plainview, Levittown, Merrick — the "
                  "Island's most-watched video haunts."},
        {"id": "nj", "label": "New Jersey Haunts", "emoji": "🎃",
         "title": "🎃 New Jersey Haunts — Virtual Tour",
         "sub": "Jersey's best video haunts — Bergen, Essex, Morris and "
                "beyond, ranked by views.",
         "blurb": "Dumont, Hawthorne, Ridgewood, Hackensack — Jersey's "
                  "most-watched video haunts."},
        {"id": "family", "label": "Family Friendly", "emoji": "🍬",
         "title": "🍬 Family Friendly — Virtual Tour",
         "sub": "All treats, no tricks — the gentlest video haunts on "
                "the map, safe for little haunters.",
         "blurb": "Family-rated video haunts nationwide — Hoboken "
                  "stoops, farm festivals and a giant LEGO skeleton."},
        {"id": "virginia", "label": "Virginia Haunts", "emoji": "⚓",
         "title": "⚓ Virginia Haunts — Virtual Tour",
         "sub": "Virginia Beach's huge haunt scene and Hampton Roads, "
                "ranked by views.",
         "blurb": "Virginia Beach alone packs 20 video haunts — plus "
                  "Chesapeake, Yorktown and Franklin."},
        {"id": "florida", "label": "Florida", "emoji": "🐊",
         "title": "🐊 Florida — Virtual Tour",
         "sub": "South Florida's best video haunts — Fort Lauderdale, "
                "Miami and beyond, ranked by views.",
         "blurb": "Pembroke Pines, Davie, Cutler Bay and Palm Bay — "
                  "Florida's most-watched video haunts."},
        {"id": "chicagoland", "label": "Chicagoland", "emoji": "🌆",
         "title": "🌆 Chicagoland — Virtual Tour",
         "sub": "Chicago and its suburbs — Naperville, Joliet, Oak "
                "Lawn — ranked by views.",
         "blurb": "Wilkes Family Halloween in Bensenville, Spirits on "
                  "Sproat and more Chicago-area haunts."},
        {"id": "texas", "label": "Texas", "emoji": "🤠",
         "title": "🤠 Texas — Virtual Tour",
         "sub": "The Lone Star State's best video haunts — San Antonio, "
                "Dallas–Fort Worth and Houston, ranked by views.",
         "blurb": "Menefee Manor, Dark Hour, Cutting Edge and more — "
                  "everything's bigger in Texas."},
        {"id": "colorado", "label": "Colorado", "emoji": "🏔️",
         "title": "🏔️ Colorado — Virtual Tour",
         "sub": "Denver-metro video haunts — Thornton, Aurora, Castle "
                "Rock — ranked by views.",
         "blurb": "Denver, Thornton, Aurora and Westminster — the Mile "
                  "High haunt run."},
        {"id": "arizona", "label": "Arizona", "emoji": "🌵",
         "title": "🌵 Arizona — Virtual Tour",
         "sub": "Phoenix-metro video haunts plus Tucson, ranked by "
                "views.",
         "blurb": "Glendale, Peoria, Chandler, Queen Creek and Tucson "
                  "— desert haunts, ranked by views."},
        {"id": "vegas", "label": "Las Vegas", "emoji": "🎰",
         "title": "🎰 Las Vegas — Virtual Tour",
         "sub": "Vegas and Boulder City video haunts — the Strip's "
                "spooky side, ranked by views.",
         "blurb": "Las Vegas home haunts plus Tom Devlin's Monster "
                  "Museum in Boulder City."},
        {"id": "bayarea", "label": "Bay Area", "emoji": "🌉",
         "title": "🌉 Bay Area — Virtual Tour",
         "sub": "San Francisco, San Jose and the Peninsula — the Bay's "
                "best video haunts, ranked by views.",
         "blurb": "San Francisco, San Jose, Palo Alto, Redwood City — "
                  "the Bay's most-watched video haunts."},
        {"id": "socal", "label": "Southern California", "emoji": "🌴",
         "title": "🌴 Southern California — Virtual Tour",
         "sub": "LA and Orange County video haunts — Burbank, Anaheim, "
                "Whittier — ranked by views.",
         "blurb": "Burbank's haunt scene, Anaheim, Mission Viejo and "
                  "more SoCal video haunts."},
    ]
    for st in sorted(state_routes, key=lambda s: VT_STATE_NAMES[s]):
        emo = VT_STATE_EMOJI.get(st, "🎃")
        channel_meta.append(
            {"id": f"state-{st.lower()}", "label": VT_STATE_NAMES[st],
             "emoji": emo,
             "title": f"{emo} {VT_STATE_NAMES[st]} — Virtual Tour",
             "sub": f"Every video haunt we have in {VT_STATE_NAMES[st]}, "
                    "ranked by views.",
             "blurb": f"{VT_STATE_NAMES[st]}'s most-watched video "
                      "haunts."})
    channels = [c for c in channel_meta if c["id"] in routes]

    def slim(stops: list[dict]) -> list[dict]:
        return [{
            "id": d["id"], "title": d["title"], "town": d["town"],
            "town_label": d["town_label"], "state": d["_state"],
            "address": d.get("address") or "",
            "lat": d["lat"], "lng": d["lng"],
            "thumb_url": d["thumb_url"], "media_url": d["media_url"],
            "media_type": d["media_type"], "kind": _vt_kind(d),
            "tiktok_url": d.get("tiktok_url") or "",
            "creator": d.get("display_name") or "",
            "scare": d.get("scare_level") or "",
            "votes": d["votes"], "views": d["_views"],
        } for d in stops]

    payload = {name: slim(stops) for name, stops in routes.items()}
    return templates.TemplateResponse(request, "virtual_tour.html",
        {"request": request, "routes": payload, "active_route": route,
         "has_scariest": "scariest" in routes,
         "channels": channels, "is_tv": is_tv})


@app.get("/tour", response_class=HTMLResponse)
def tour_page(request: Request, s: str = "", cat: str = "halloween"):
    cat = cat if cat in CATEGORIES else "halloween"
    shared: list = []
    if s.strip():
        try:
            ids = [int(x) for x in s.split(",") if x.strip().isdigit()][:50]
        except ValueError:
            ids = []
        if ids:
            with get_conn(DB_PATH) as conn:
                rows = conn.execute(
                    f"SELECT * FROM entries WHERE hidden = 0 AND category = ? "
                    f"AND id IN ({','.join('?' * len(ids))})",
                    [cat] + ids).fetchall()
            by_id = {r["id"]: row_to_dict(r) for r in rows}
            shared = [by_id[i] for i in ids if i in by_id]
    return templates.TemplateResponse(request, "tour.html",
        {"request": request, "shared": shared, "shared_ids": s,
         "cat": cat, "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI},
    )


# ---------------------------------------------------------------- shared tours
# Item 8 (retention Wave 5): persistent, public "My Fright Night" itinerary
# pages. The pre-Item-8 share mechanism was stateless: the tour page built
# /tour?s=<comma-separated pin ids> entirely client-side and GET /tour above
# re-resolved the ids per load. Nothing was stored, so links carried no
# title, no landing page, and no view count — and a hidden/deleted pin
# silently vanished from the link. That route is KEPT untouched (old links
# in the wild keep resolving); the new default below stores the tour
# server-side behind a short slug: POST /api/tours -> /t/{slug}.

SHARED_TOUR_MAX_STOPS = 50


def _shared_tour_title(entries: list[dict], requested) -> str:
    """Title rule: an explicit non-empty title wins (trimmed, 80 chars).
    Otherwise 'My Fright Night', enriched with the town label when at
    least half the stops share one town_label ('My Fright Night —
    Seekonk, MA')."""
    if isinstance(requested, str) and requested.strip():
        return requested.strip()[:80]
    counts: dict[str, int] = {}
    for e in entries:
        label = e.get("town_label") or ""
        if label:
            counts[label] = counts.get(label, 0) + 1
    if counts:
        top_label, top_n = max(counts.items(), key=lambda kv: kv[1])
        if top_n * 2 >= len(entries):
            return f"My Fright Night — {top_label}"
    return "My Fright Night"


def _visible_tour_entries(ids: list[int]) -> list[dict]:
    """Resolve pin ids to visible entries in the given order. Missing,
    hidden, and coord-less pins are dropped (a tour stop needs coords for
    the map, the directions link, and the /tour copy target — the tour
    builder itself only ever holds coord-ful entries)."""
    if not ids:
        return []
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            f"SELECT * FROM entries WHERE hidden = 0 "
            f"AND id IN ({','.join('?' * len(ids))})", ids).fetchall()
    by_id = {r["id"]: row_to_dict(r) for r in rows}
    return [by_id[i] for i in ids
            if i in by_id and by_id[i].get("lat") and by_id[i].get("lng")]


@app.post("/api/tours")
async def api_create_shared_tour(request: Request):
    """Create a persistent shared tour. Body: {pin_ids: [...], title?}.
    Validates that ids exist, are visible, and carry coords; de-dupes
    keeping first occurrence; caps at SHARED_TOUR_MAX_STOPS; needs >= 2
    valid stops. Returns {slug, url, title, stops}."""
    try:
        data = await request.json()
    except Exception:
        data = {}
    if not isinstance(data, dict):
        data = {}
    ids: list[int] = []
    for x in data.get("pin_ids") or []:
        try:
            i = int(x)
        except (TypeError, ValueError):
            continue
        if i not in ids:
            ids.append(i)
    ids = ids[:SHARED_TOUR_MAX_STOPS]
    entries = _visible_tour_entries(ids)
    if len(entries) < 2:
        return JSONResponse(
            {"error": "A shared tour needs at least 2 stops that are still on the map."},
            status_code=400)
    title = _shared_tour_title(entries, data.get("title"))
    pin_ids_json = json.dumps([e["id"] for e in entries])
    with get_conn(DB_PATH) as conn:
        slug = None
        for _ in range(5):  # collision-checked slug minting
            cand = secrets.token_urlsafe(6)  # 8 URL-safe chars
            if not conn.execute("SELECT 1 FROM shared_tours WHERE slug = ?",
                                (cand,)).fetchone():
                slug = cand
                break
        if slug is None:
            return JSONResponse({"error": "Could not create a tour link — try again."},
                                status_code=500)
        conn.execute(
            "INSERT INTO shared_tours (slug, title, pin_ids, created_at) "
            "VALUES (?, ?, ?, ?)",
            (slug, title, pin_ids_json, datetime.now(timezone.utc).isoformat()))
        conn.commit()
    return JSONResponse({"slug": slug, "url": f"/t/{slug}",
                         "title": title, "stops": len(entries)})


@app.get("/t/{slug}", response_class=HTMLResponse)
def shared_tour_page(request: Request, slug: str):
    """Public itinerary page for a shared tour. Increments the tour's view
    counter per load (Jarvis's HauntMap-Verify checks excluded, matching
    the page_views middleware). Pins hidden/deleted since sharing are
    skipped and the shortfall is surfaced on the page — never a 500."""
    with get_conn(DB_PATH) as conn:
        row = conn.execute("SELECT * FROM shared_tours WHERE slug = ?",
                           (slug,)).fetchone()
        if row is None:
            return templates.TemplateResponse(
                request, "shared_tour_404.html", {"request": request},
                status_code=404)
        if "HauntMap-Verify" not in request.headers.get("user-agent", ""):
            conn.execute("UPDATE shared_tours SET views = views + 1 WHERE slug = ?",
                         (slug,))
            conn.commit()
        try:
            ids = [int(x) for x in json.loads(row["pin_ids"] or "[]")]
        except (TypeError, ValueError):
            ids = []
    stops = _visible_tour_entries(ids)
    missing = len(ids) - len(stops)
    # Google Maps directions, built exactly like the tour page's openGMaps
    # (origin = first stop, destination = last, middle stops as
    # waypoints) with driving mode — a shared itinerary is a drive plan.
    gmaps_url = ""
    if len(stops) >= 2:
        origin = f"{stops[0]['lat']},{stops[0]['lng']}"
        dest = f"{stops[-1]['lat']},{stops[-1]['lng']}"
        waypoints = "|".join(f"{e['lat']},{e['lng']}" for e in stops[1:-1])
        gmaps_url = ("https://www.google.com/maps/dir/?api=1"
                     f"&origin={origin}&destination={dest}&travelmode=driving")
        if waypoints:
            gmaps_url += f"&waypoints={waypoints}"
    # Payload for "Copy this tour": the exact localStorage haunt_tour
    # entry format the tour builder reads ({id,title,town,lat,lng,thumb}).
    copy_entries = [{"id": e["id"], "title": e["title"], "town": e["town"],
                     "lat": e["lat"], "lng": e["lng"],
                     "thumb": e.get("thumb_url") or ""} for e in stops]
    return templates.TemplateResponse(request, "shared_tour.html",
        {"request": request, "tour_title": row["title"], "slug": slug,
         "stops": stops, "missing": missing, "gmaps_url": gmaps_url,
         "copy_entries": copy_entries})



# Street-address gate for /upload (Dan, Oct 26): pin 5973 ("Demon Tree",
# Maryland) went live from the public form with NO street address and NO
# coordinates — its page existed but directions pointed at "None,None" and
# it could not be plotted or routed to. Rule from here on: no street
# address, no upload. A street address = house number + street name; a
# town or ZIP alone is not an address. The number may carry a unit letter
# ("123A"); the street part must contain a letter (so "123 4" fails).
_STREET_ADDRESS_RE = re.compile(r"^\d{1,6}(?:-\d{1,5})?[A-Za-z]?\s+\S+.*[A-Za-z]", re.DOTALL)

# UK addresses (Oct 27 — first UK pin: Ffear Fforest, Zip World
# Betws-y-Coed): rural UK venues routinely have NO house number; their
# routable street address is the road designator/name + the full UK
# postcode (the postcode is the routing key — Nominatim resolves it to
# the venue). Accept that shape as a street address too: a UK postcode
# AND a road token (an A/B-road designator like "A470", or a street /
# road / lane word). The Nominatim geocode + town-anchor checks below
# still gate every submission, exactly as on the US path.
_UK_POSTCODE_RE = re.compile(r"\b[A-Za-z]{1,2}\d[A-Za-z\d]?\s*\d[A-Za-z]{2}\b")
_UK_ROAD_RE = re.compile(
    r"\b(?:[ABM]\d{1,4}|street|road|lane|avenue|drive|way|close|place|"
    r"square|hill|bridge)\b", re.IGNORECASE)

ADDRESS_REQUIRED_MSG = ("We need the street address — e.g. 123 Main St — "
                        "so visitors can find it on the map.")
ADDRESS_NOT_FOUND_MSG = ("We couldn't find that street address on the map — "
                         "please check it and try again. " + ADDRESS_REQUIRED_MSG)


def looks_like_street_address(address: str) -> bool:
    a = (address or "").strip()
    if _STREET_ADDRESS_RE.match(a):
        return True
    # UK shape: road designator/name + full postcode, no house number.
    return bool(_UK_POSTCODE_RE.search(a) and _UK_ROAD_RE.search(a))


@app.post("/upload", response_class=HTMLResponse)
async def upload_submit(
    request: Request,
    title: str = Form(""),
    town: str = Form(""),
    display_name: str = Form(""),
    category: str = Form("halloween"),
    scare_level: str = Form(""),
    lat: str = Form(""),
    lng: str = Form(""),
    tiktok_url: str = Form(""),
    address: str = Form(""),
    description: str = Form(""),
    uploader_email: str = Form(""),
    virtual: str = Form(""),
    media: UploadFile = File(None),
):
    error: str | None = None
    title, town, display_name = title.strip()[:120], town.strip()[:80], display_name.strip()[:40]
    # address/description must be declared here — FastAPI silently drops
    # undeclared form fields, which is how crew uploads lost them (Oct 2026).
    address = address.strip()[:200]
    description = description.strip()[:1000]
    category = category if category in CATEGORIES else "halloween"
    # Virtual LIVE exemption (Dan, Oct 27): a category="live" entry that
    # is an online-only room (e.g. a TikTok quiz stream with no physical
    # venue) may post with NO street address and NO coordinates. The flag
    # is honoured ONLY for live — every other category keeps the
    # street-address mandate below, flag or not. A virtual entry's town
    # is server-set to the display basis "Online / Virtual"; no address
    # is stored and nothing is fabricated, so the pin carries no coords
    # and stays out of the map, tours and Auto Tour (all of which
    # require coordinates and/or a verified address) by construction.
    is_virtual = 1 if (category == "live" and (virtual or "").strip()) else 0
    if is_virtual:
        town = "Online / Virtual"
        address = ""
    scare_level = scare_level if scare_level in ("family", "spooky", "creepy", "terrifying", "extreme") else None
    # tags come as repeated form fields from checkboxes
    form = await request.form()
    uploader_email = uploader_email.strip().lower()[:120]
    if "@" not in uploader_email:
        uploader_email = ""
    notify_votes = 1 if form.get("notify_votes") else 0
    tags = ",".join(sorted({t for t in form.getlist("tags")
                            if t in ("animatronics", "inflatables", "handmade", "walkthrough",
                                     "projector", "lights", "music", "street-wide",
                                     "multi-house", "ticketed", "2025", "market", "oddities", "witchy", "craft", "flea", "free", "flagship", "21+")})) or None

    lat_f = lng_f = None
    if is_virtual:
        pass  # virtual LIVE rooms are coord-less by definition (see above)
    elif lat.strip() or lng.strip():
        try:
            lat_f, lng_f = float(lat), float(lng)
            if not (-90 <= lat_f <= 90 and -180 <= lng_f <= 180):
                raise ValueError
        except ValueError:
            error = "Map pin coordinates look invalid — please try again."

    if not error and not title:
        error = "Please give your haunt a title."
    if not error and not is_virtual and not town:
        error = "Please add a town or neighborhood."
    # Street address is MANDATORY (Dan, Oct 26 — see _STREET_ADDRESS_RE):
    # missing or not a street address (house number + street name) rejects.
    # Sole exception: virtual LIVE rooms (is_virtual, set above) skip the
    # address + geocode gates entirely and are born with NULL coords.
    if not error and not is_virtual and not looks_like_street_address(address):
        error = ADDRESS_REQUIRED_MSG
    # Geocode the address at submission so the pin is born with coordinates
    # and plots + routes immediately. The geocoded point is authoritative:
    # it replaces any form-supplied lat/lng. An address that cannot be
    # geocoded rejects rather than storing an unplottable pin.
    if not error and not is_virtual:
        geo = geocode_nominatim(f"{address}, {town}") or geocode_nominatim(address)
        # Nominatim fuzzy-matches: a bogus street name can resolve to a
        # same-named street on another continent (rig test: "999999 Nowhere
        # Lane" + Hackensack -> Nailsea, England). Anchor the result to the
        # stated town: if the town itself geocodes and the address point
        # lands nowhere near it, treat the address as not found.
        if geo is not None:
            town_geo = geocode_nominatim(town)
            if town_geo is not None and haversine_miles(
                    geo[0], geo[1], town_geo[0], town_geo[1]) > 60:
                geo = None
        if geo is None:
            error = ADDRESS_NOT_FOUND_MSG
        else:
            lat_f, lng_f = geo
    if not error and (not media or not media.filename) and category not in ("events", "halloween_stores", "live"):
        error = "Please attach a photo or video."

    entry_id = None
    has_media = media and media.filename
    if not error:
        # Media processing (PIL decode, EXIF transpose, thumbnailing, an
        # ffmpeg poster frame that can take seconds) and the insert run
        # in the thread pool, never on the event loop (blip hardening,
        # Oct 25) — code below is the original flow, moved verbatim.
        def _store() -> tuple[int | None, str | None]:
            media_rel = None
            thumb_rel = None
            media_type = None
            if has_media:
                ext = safe_ext(media.filename)
                try:
                    if ext in PHOTO_EXTS:
                        tmp = save_upload(media, MAX_PHOTO_BYTES)
                        try:
                            with Image.open(tmp) as im:
                                im.verify()
                        except (UnidentifiedImageError, OSError):
                            tmp.unlink(missing_ok=True)
                            raise ValueError("That file isn't a readable image.")
                        name = uuid.uuid4().hex
                        media_rel = f"{name}{ext}"
                        shutil.move(tmp, UPLOAD_DIR / media_rel)
                        try:
                            thumb_rel = make_thumb(UPLOAD_DIR / media_rel, name)
                        except (OSError, UnidentifiedImageError):
                            (UPLOAD_DIR / media_rel).unlink(missing_ok=True)
                            raise ValueError("Couldn't process that image.")
                        media_type = "photo"
                    elif ext in VIDEO_EXTS:
                        tmp = save_upload(media, MAX_VIDEO_BYTES)
                        head = tmp.read_bytes()[:32]
                        if b"ftyp" not in head:
                            tmp.unlink(missing_ok=True)
                            raise ValueError("That file doesn't look like an MP4 video.")
                        name = uuid.uuid4().hex
                        media_rel = f"{name}{ext}"
                        shutil.move(tmp, UPLOAD_DIR / media_rel)
                        thumb_rel = make_video_poster(UPLOAD_DIR / media_rel, name)
                        media_type = "video"
                    else:
                        raise ValueError("Photos must be JPG/PNG/WebP (10 MB max); video must be MP4 (100 MB max).")
                except ValueError as e:
                    return None, str(e)
            now = datetime.now(timezone.utc).isoformat()
            with get_conn(DB_PATH) as conn:
                for col, ddl in (("uploader_email", "TEXT"),
                                 ("notify_votes", "INTEGER DEFAULT 0"),
                                 ("virtual", "INTEGER NOT NULL DEFAULT 0")):
                    try:
                        conn.execute(f"ALTER TABLE entries ADD COLUMN {col} {ddl}")
                    except Exception:
                        pass  # column already exists
                cur = conn.execute(
                    """INSERT INTO entries
                       (title, town, display_name, media_path, thumb_path, media_type,
                        lat, lng, votes, flagged, hidden, is_sample, category, created_at,
                        scare_level, tags, tiktok_url, uploader_email, notify_votes,
                        address, description, virtual)
                       VALUES (?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0, 0, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                    (title, town, display_name or None, media_rel or "", thumb_rel,
                     media_type or "none", lat_f, lng_f, category, now, scare_level, tags,
                     tiktok_url or None, uploader_email or None, notify_votes,
                     address or None, description or None, is_virtual),
                )
                new_id = cur.lastrowid
                # Multi-video pins (Oct 27): the uploaded pin's TikTok
                # becomes position 0 of its entry_videos list (the
                # tiktok_url column set above stays the primary mirror).
                if tiktok_url:
                    add_entry_video(conn, new_id, tiktok_url)
                conn.commit()
            return new_id, None

        entry_id, store_error = await run_in_threadpool(_store)
        if store_error:
            error = store_error

    if error:
        # Re-render with the uploader's other entries intact so a rejected
        # address doesn't cost them the whole form (the photo/video itself
        # cannot survive a form reload — the template says so under the
        # alert).
        values = {
            "category": category, "title": title, "town": town,
            "display_name": display_name, "uploader_email": uploader_email,
            "address": address, "scare_level": scare_level or "",
            "virtual": bool(is_virtual),
            "tags": set(tags.split(",")) if tags else set(),
            "notify_votes": bool(notify_votes),
        }
        return templates.TemplateResponse(request, "upload.html", {"request": request, "error": error, "values": values}, status_code=400
        )
    # Frank announces the site (brief §4): the room hears about the
    # new listing, throttled + batched inside the helper.
    if entry_id:
        _frank_announce_new_listing(entry_id)
    return RedirectResponse(f"/d/{entry_id}", status_code=303)


# ------------------------------------------------- engagement events (Wave 2, Item 2)
# Lightweight interaction log alongside page_views: page loads alone can't
# see in-page behaviour (video plays, tour adds, votes that no longer
# reload), so the interactions worth optimising for get their own rows.
# Client-fired events arrive via POST /api/track; vote/unvote/scare/tip are
# ALSO logged server-side in their POST handlers so those counts never
# depend on JS surviving.
ENGAGEMENT_TABLE_SQL = (
    "CREATE TABLE IF NOT EXISTS engagement_events "
    "(id INTEGER PRIMARY KEY AUTOINCREMENT, created_at TEXT NOT NULL, "
    "event TEXT NOT NULL, entry_id INTEGER, town TEXT, path TEXT, "
    "seconds INTEGER, sid TEXT, source TEXT, pvid TEXT)"
)
# Whitelist for POST /api/track — anything else is a silent no-op.
TRACK_EVENTS = ("video_play", "tour_add", "next_bar_click", "rail_click")
# Retention Wave 2, Item 6: engaged-time beacon. Deliberately NOT in
# TRACK_EVENTS / ENGAGEMENT_EVENTS_ALL: those are pin interactions counted
# per-row on the admin stats page, while 'engaged' rows each carry a
# SECONDS value that must be SUM-med, not counted (see _log_engaged).
# sid is the visitor's existing hm_sid cookie — the same anonymous session
# id page_views already stores; no new identifier is minted or stored.
ENGAGED_EVENT = "engaged"
# Per-beacon clamp: the client heartbeats every 15s of engaged time, so a
# single beacon claiming more than 60s is a stalled tab or garbage.
ENGAGED_MAX_SECONDS = 60
# Full taxonomy shown on the admin stats page (client + server events).
ENGAGEMENT_EVENTS_ALL = TRACK_EVENTS + ("vote", "unvote", "scare", "tip")
# Rail Boost (Oct 25): per-rail attribution for rail_click. The pin-page
# click handler in base.html reads the clicked card's rail container
# (data-rail attribute in detail.html) and sends it as `source`; only
# these values are stored — anything else is dropped to NULL so the
# stats breakdown can never be polluted by client garbage.
RAIL_SOURCES = ("footage", "town", "near", "near-here", "like-this", "explore")
# Rail impression beacons (Rail Boost research addendum, Oct 25): one
# row per rail per page view, fired client-side when a rail is >=50%
# visible — the denominator for honest per-rail CTR on the stats page.
# Deliberately NOT in TRACK_EVENTS / ENGAGEMENT_EVENTS_ALL (same
# discipline as 'engaged'): impressions are not pin interactions, and
# counting them as such would inflate the interactions/pin-visit ratio.
RAIL_IMPRESSION_EVENT = "rail_impression"


def _log_engagement(event: str, entry_id: int | None = None,
                    source: str | None = None) -> None:
    """Record one engagement row. Town is derived server-side from the
    entry (its extract_city_state label) by the analytics writer at
    flush time. `source` is the Rail Boost rail name for rail_click
    rows, NULL for everything else. Fire-and-forget: analytics must
    never break the interaction that produced the event. Enqueue only
    — the request path never touches the DB inline (blip hardening,
    Oct 25)."""
    try:
        _analytics_q.put(("eng", datetime.now(timezone.utc).isoformat(),
                          event, entry_id, source))
    except Exception:
        pass


def _log_engaged(seconds: int, path: str, sid: str | None,
                 pvid: str | None = None) -> None:
    """Record one engaged-time beacon row: `seconds` of INCREMENTAL engaged
    time (client sends deltas, never cumulative totals) spent on `path`.
    Real time-on-page per page/session is SUM(seconds) over these rows —
    e.g. SELECT path, SUM(seconds) FROM engagement_events
    WHERE event='engaged' GROUP BY path. `pvid` is the beacon's random
    per-page-load id: grouping rows by it reconstructs ONE page view's
    total dwell, which is what the admin per-page time table medians
    over (per-page time stats, Oct 25). Fire-and-forget like
    _log_engagement: analytics must never break a page. Enqueue only
    (blip hardening, Oct 25)."""
    try:
        _analytics_q.put(("engaged", datetime.now(timezone.utc).isoformat(),
                          seconds, path, sid, pvid))
    except Exception:
        pass


def _wants_json(request: Request) -> bool:
    """True when a POST wants the in-place (fetch) response instead of the
    classic redirect: the detail page's fetch interceptor sends
    X-Requested-With: fetch (and an application/json Accept)."""
    if request.headers.get("x-requested-with", "").strip().lower() == "fetch":
        return True
    return "application/json" in request.headers.get("accept", "")


def _scare_counts_for(entry_id: int) -> tuple[dict, int]:
    counts = {lvl: 0 for lvl in SCARE_LEVELS}
    with get_conn(DB_PATH) as conn:
        conn.execute(SCARE_TABLE_SQL)
        for r in conn.execute(
                "SELECT level, votes FROM scare_votes WHERE entry_id = ?", (entry_id,)):
            if r["level"] in counts:
                counts[r["level"]] = r["votes"]
    return counts, sum(counts.values())


@app.post("/api/track")
async def api_track(request: Request):
    """Beacon endpoint for client-side engagement events. Accepts a JSON
    body {event, entry_id} — or {event:'engaged', seconds, path, pvid} for
    the Item 6 time-on-page beacon. navigator.sendBeacon posts as text/plain,
    so the raw body is parsed, never request.json()/form. Whitelisted
    events only; always 204 with no body, malformed input included, so a
    tracking failure can never surface on a page."""
    try:
        raw = await request.body()
        data = json.loads(raw.decode("utf-8", "replace")) if raw else {}
        if not isinstance(data, dict):
            data = {}
        event = str(data.get("event") or "")
        if event == ENGAGED_EVENT:
            # Item 6 beacon: {event:'engaged', seconds:<int>, path:</x>}.
            # Garbage is dropped silently, same as every other event here:
            # non-numeric or non-positive seconds never land; oversized
            # claims clamp to ENGAGED_MAX_SECONDS instead of inflating
            # totals; only a bare path is stored — query/fragment (which
            # could carry tokens) are stripped, length capped.
            try:
                seconds = int(data.get("seconds"))
            except (TypeError, ValueError):
                seconds = 0
            seconds = max(0, min(seconds, ENGAGED_MAX_SECONDS))
            path = str(data.get("path") or "")
            path = path.split("?")[0].split("#")[0][:500]
            # Per-page-load id (per-page time stats, Oct 25): minted by
            # the beacon per page load; kept to lowercase alphanumerics
            # and capped, anything else becomes None (row still lands —
            # it just can't join a per-view dwell group).
            pvid = re.sub(r"[^a-z0-9]", "", str(data.get("pvid") or "").lower())[:40] or None
            if seconds > 0 and path.startswith("/"):
                _log_engaged(seconds, path, request.cookies.get("hm_sid"), pvid)
        elif event == RAIL_IMPRESSION_EVENT:
            # {event:'rail_impression', source:<rail>} — whitelisted rail
            # names only; no entry_id (the impression belongs to the
            # rail on whatever pin page rendered it, not to a pin).
            raw_src = str(data.get("source") or "")
            if raw_src in RAIL_SOURCES:
                _log_engagement(RAIL_IMPRESSION_EVENT, None, raw_src)
        elif event in TRACK_EVENTS:
            entry_id = data.get("entry_id")
            try:
                entry_id = int(entry_id) if entry_id is not None else None
            except (TypeError, ValueError):
                entry_id = None
            # Rail Boost: per-rail attribution rides along on rail_click
            # only, whitelisted — an unknown or absent source stores NULL
            # (the pre-Rail-Boost rows read the same way on the stats page).
            source = None
            if event == "rail_click":
                raw_src = str(data.get("source") or "")
                if raw_src in RAIL_SOURCES:
                    source = raw_src
            _log_engagement(event, entry_id, source)
    except Exception:
        pass
    return Response(status_code=204)


# ------------------------------------------------------- keep exploring
# Rail Boost (Oct 25), Item 6: the pin page's endless tail. The client
# sends the ids already on the page (every rail + previous batches) and
# gets the next batch of same-category pins nearest THIS pin, rendered
# server-side through the same _pin_card macro the rails use — so an
# explore card is pixel-identical to a rail card, and its clicks track
# as rail_click (source=explore) via the base.html handler. Button-
# driven on the client (no auto-scroll): each click is one batch.
EXPLORE_BATCH = 8


@app.get("/api/explore")
def api_explore(request: Request, from_id: int, exclude: str = ""):
    entry = get_entry(from_id)
    empty = {"html": "", "ids": [], "done": True}
    if (not entry or entry.get("hidden") or entry.get("lat") is None
            or entry.get("lng") is None):
        return JSONResponse(empty)
    seen = {from_id}
    for tok in (exclude or "").split(",")[:800]:
        tok = tok.strip()
        if tok.isdigit():
            seen.add(int(tok))
    peers = [p for p in category_peers(entry)
             if p["id"] not in seen
             and p.get("lat") is not None and p.get("lng") is not None]
    for p in peers:
        p["distance"] = haversine_miles(entry["lat"], entry["lng"],
                                        p["lat"], p["lng"])
    peers.sort(key=lambda p: (p["distance"], p["id"]))
    # Near-rail cap (Dan, Oct 25): the tail serves only visitable
    # pins — when the within-cap pool runs out the endpoint reports
    # done and the section's own copy takes over ("You've seen
    # everything near here — the map has the rest of the country").
    peers = [p for p in peers if p["distance"] <= NEAR_RAIL_CAP_MI]
    if entry.get("category") in RESTAURHAUNT_CATS:
        # Restaurhaunts ordering (Dan, Oct 26): decked-first inside
        # the capped near set; distance breaks ties.
        peers.sort(key=lambda p: (-decked_score(p), p["distance"], p["id"]))
    batch = peers[:EXPLORE_BATCH]
    if not batch:
        return JSONResponse(empty)
    with get_conn(DB_PATH) as conn:
        views = _views_by_id(conn)
    hot_ids = _hot_view_ids(views)
    for p in batch:
        p["_views"] = views.get(p["id"], 0)
        _apply_card_badge(p, hot_ids)
    card_tpl = templates.env.get_template("_pin_card.html")
    html = "".join(str(card_tpl.module.pin_card(p, True)) for p in batch)
    return JSONResponse({"html": html, "ids": [p["id"] for p in batch],
                         "done": len(batch) < EXPLORE_BATCH})


@app.get("/d/{entry_id}", response_class=HTMLResponse)
def detail(request: Request, entry_id: int):
    entry = get_entry(entry_id)
    if not entry or entry["hidden"]:
        raise HTTPException(404, "Entry not found.")
    # Multi-video pins (Oct 27): the primary (entries.tiktok_url) plays
    # in the hero; every OTHER video of this place renders below it in
    # the "More videos of this place" facades. Empty for the one-video
    # pins that make up nearly the whole site — the page is unchanged
    # for them.
    with get_conn(DB_PATH) as conn:
        _all_videos = get_entry_videos(conn, entry_id)
    _primary_vid = tiktok_video_id(entry.get("tiktok_url"))
    extra_videos = [v for v in _all_videos if v["video_id"] != _primary_vid]
    voted = f"voted_{entry_id}" in request.cookies
    reported = f"reported_{entry_id}" in request.cookies
    with get_conn(DB_PATH) as conn:
        tips = [dict(r) for r in conn.execute(
            "SELECT display_name, text, created_at FROM comments "
            "WHERE entry_id = ? AND hidden = 0 ORDER BY created_at DESC LIMIT 50",
            (entry_id,)).fetchall()]
        conn.execute(SCARE_TABLE_SQL)
        scare_counts = {lvl: 0 for lvl in SCARE_LEVELS}
        for r in conn.execute(
                "SELECT level, votes FROM scare_votes WHERE entry_id = ?", (entry_id,)):
            if r["level"] in scare_counts:
                scare_counts[r["level"]] = r["votes"]
    scare_total = sum(scare_counts.values())
    scare_pick = request.cookies.get(f"scare_{entry_id}", "")
    if scare_pick not in SCARE_LEVELS:
        scare_pick = ""
    chain = detail_chain(entry)
    # Retention Wave 1, Item 3 (+ Dan's Oct 23 most-viewed-first /
    # location-first revision in detail_chain): on a pin WITH footage,
    # the primary Next target (big button + sticky bar + prerender) is
    # the most-viewed pin WITH footage within VIDEO_CHAIN_RADIUS_MI —
    # of the visitor when their town is known (client-side re-pick in
    # detail.html), else of this pin; otherwise — and on every
    # non-footage pin — it is exactly today's geographic next. The
    # bottom prev/next chain-nav keeps the geographic target either
    # way (passed as next_geo_pin).
    geo_next_pin = chain["next_pin"]
    video_next_pin = chain.get("next_video_pin")
    effective_next_pin = video_next_pin or geo_next_pin
    # Engagement next-steps section (staged Oct 22): the 3 nearest neighbours
    # for the prominent "More haunts near this one" block. Real-media pins
    # (an actual uploaded photo/video — i.e. not stock-photo pins, which sit
    # in DUEL_EXCLUDE_IDS) rank ahead of stock ones at equal distance.
    if entry.get("category") in RESTAURHAUNT_CATS:
        # Restaurhaunts ordering (Dan, Oct 26): decked-first inside the
        # near set — real-media first (existing rule), then the most
        # decked venues, then distance.
        more_haunts = sorted(
            chain["more_near"],
            key=lambda p: (1 if p["id"] in DUEL_EXCLUDE_IDS else 0,
                           -decked_score(p), p["distance"]),
        )[:3]
    else:
        more_haunts = sorted(
            chain["more_near"],
            key=lambda p: (1 if p["id"] in DUEL_EXCLUDE_IDS else 0, p["distance"]),
        )[:3]
    # Collection loop: ids of every visible pin in this pin's town + category,
    # so the page can show "You've seen X of Y displays in [Town]" (the
    # seen-set itself lives in the visitor's localStorage — no accounts).
    entry_label = extract_city_state(entry["town"] or "") or entry["town"] or ""
    # Town rail rows from the shared cached snapshots (fortification
    # pass 2): _entries_with_views composes the cached category row set
    # with the cached _views_by_id — the same row dicts (incl. _views)
    # the per-render GROUP BY join used to produce here.
    with get_conn(DB_PATH) as conn:
        town_rows = _entries_with_views(conn, entry["category"])
    town_pin_ids = []
    town_haunts = []
    for p in town_rows:
        if (extract_city_state(p["town"] or "") or p["town"] or "") != entry_label:
            continue
        town_pin_ids.append(p["id"])
        if p["id"] != entry_id:
            town_haunts.append(p)
    # Rail Boost: town-rail cards carry the distance from this pin (when
    # both have coordinates) and the shared card badge, like every rail.
    with get_conn(DB_PATH) as conn:
        _town_hot = _hot_view_ids(_views_by_id(conn))
    for p in town_haunts:
        if (entry.get("lat") is not None and entry.get("lng") is not None
                and p.get("lat") is not None and p.get("lng") is not None):
            p["distance"] = haversine_miles(entry["lat"], entry["lng"],
                                            p["lat"], p["lng"])
        _apply_card_badge(p, _town_hot)
    # Second-click recirculation rail: same town, real thumbnails first,
    # then most-viewed, then most-voted. Excludes the pin itself.
    town_haunts.sort(key=lambda p: (0 if p.get("thumb_url") else 1,
                                    -p.get("_views", 0), -p.get("votes", 0),
                                    p["id"]))
    town_haunts = town_haunts[:6]
    # Item 7: _views STAYS on town_haunts (it used to be popped here) —
    # the town rail renders through _pin_card.html, which shows the
    # count on video cards.
    return templates.TemplateResponse(request, "detail.html",
        {"request": request, "entry": entry, "voted": voted, "reported": reported,
         "extra_videos": extra_videos,
         "is_venue": entry["category"] in VENUE_CATS,
         "tips": tips, "scare_counts": scare_counts, "scare_total": scare_total,
         "scare_pick": scare_pick, "next_pin": effective_next_pin,
         "next_geo_pin": geo_next_pin,
         "next_is_video": bool(video_next_pin),
         "video_chain": chain.get("video_chain", []),
         "town_centers": chain.get("town_centers", []),
         "prev_pin": chain["prev_pin"], "more_near": chain["more_near"],
         "more_like": chain["more_like"], "town_pin_ids": town_pin_ids,
         "more_haunts": more_haunts, "town_haunts": town_haunts,
         "bracket_info": ({"seed": brk.SEED_OF[entry_id],
                           "region": brk.REGIONS.get(entry_id, "")}
                          if entry_id in brk.SEED_OF else None)},
    )


SCARE_LEVELS = ("family", "spooky", "creepy", "terrifying", "extreme")
SCARE_TABLE_SQL = (
    "CREATE TABLE IF NOT EXISTS scare_votes "
    "(entry_id INTEGER, level TEXT, votes INTEGER DEFAULT 0, "
    "PRIMARY KEY (entry_id, level))"
)


@app.post("/d/{entry_id}/scare/{level}")
def scare_vote(entry_id: int, level: str, request: Request):
    entry = get_entry(entry_id)
    if not entry or entry["hidden"]:
        raise HTTPException(404, "Entry not found.")
    if entry["category"] in VENUE_CATS:
        # Venues have no Scare-O-Meter (Dan, Oct 25): refuse API-style
        # calls, silently ignore stale form posts. Nothing is written.
        if _wants_json(request):
            return JSONResponse({"ok": False, "error": "venues have no scare meter"},
                                status_code=403)
        return RedirectResponse(f"/d/{entry_id}", status_code=303)
    if level not in SCARE_LEVELS:
        raise HTTPException(400, "Bad scare level.")
    cookie = f"scare_{entry_id}"
    old = request.cookies.get(cookie, "")
    changed = old != level
    if changed:
        with get_conn(DB_PATH) as conn:
            conn.execute(SCARE_TABLE_SQL)
            if old in SCARE_LEVELS:
                conn.execute(
                    "UPDATE scare_votes SET votes = MAX(votes - 1, 0) "
                    "WHERE entry_id = ? AND level = ?", (entry_id, old))
            conn.execute(
                """INSERT INTO scare_votes (entry_id, level, votes) VALUES (?, ?, 1)
                   ON CONFLICT(entry_id, level) DO UPDATE SET votes = votes + 1""",
                (entry_id, level))
            conn.commit()
        _log_engagement("scare", entry_id)
    if _wants_json(request):
        counts, total = _scare_counts_for(entry_id)
        resp = JSONResponse({"ok": True, "counts": counts, "total": total,
                             "pick": level})
        if changed:
            resp.set_cookie(cookie, level, max_age=365 * 24 * 3600,
                            httponly=True, samesite="lax")
        return resp
    resp = RedirectResponse(f"/d/{entry_id}#scare", status_code=303)
    if changed:
        resp.set_cookie(cookie, level, max_age=365 * 24 * 3600,
                        httponly=True, samesite="lax")
    return resp


@app.post("/d/{entry_id}/tip")
async def add_tip(entry_id: int, request: Request):
    entry = get_entry(entry_id)
    if not entry or entry["hidden"]:
        raise HTTPException(404, "Entry not found.")
    form = await request.form()
    text = form.get("text", "").strip()[:500]
    name = form.get("display_name", "").strip()[:40] or None
    if text:
        with get_conn(DB_PATH) as conn:
            conn.execute(
                "INSERT INTO comments (entry_id, display_name, text, created_at) "
                "VALUES (?, ?, ?, ?)",
                (entry_id, name, text, datetime.now(timezone.utc).isoformat()),
            )
            conn.commit()
        _log_engagement("tip", entry_id)
        if _wants_json(request):
            return JSONResponse({"ok": True, "tip": {
                "display_name": name or "Anonymous", "text": text}})
    elif _wants_json(request):
        return JSONResponse({"ok": False, "error": "empty tip"}, status_code=400)
    return RedirectResponse(f"/d/{entry_id}#tips", status_code=303)


@app.post("/d/{entry_id}/vote")
def vote(entry_id: int, request: Request):
    entry = get_entry(entry_id)
    if not entry or entry["hidden"]:
        raise HTTPException(404, "Entry not found.")
    if entry["category"] in VENUE_CATS:
        # Venues have no haunt vote (Dan, Oct 25): refuse API-style
        # calls, silently ignore stale form posts. Nothing is written.
        if _wants_json(request):
            return JSONResponse({"ok": False, "error": "venues have no haunt vote"},
                                status_code=403)
        return RedirectResponse(f"/d/{entry_id}", status_code=303)
    cookie = f"voted_{entry_id}"
    # Soft limit: one vote per browser. Clearing cookies bypasses it — by design
    # for v1 (no accounts). Good enough to stop casual double-voting.
    fresh_vote = cookie not in request.cookies
    if fresh_vote:
        with get_conn(DB_PATH) as conn:
            conn.execute("UPDATE entries SET votes = votes + 1 WHERE id = ?", (entry_id,))
            conn.commit()
        _log_engagement("vote", entry_id)
    if _wants_json(request):
        now = get_entry(entry_id)
        resp = JSONResponse({"ok": True,
                             "votes": now["votes"] if now else entry["votes"],
                             "voted": True})
        if fresh_vote:
            resp.set_cookie(cookie, "1", max_age=365 * 24 * 3600, httponly=True, samesite="lax")
        return resp
    resp = RedirectResponse(f"/d/{entry_id}", status_code=303)
    if fresh_vote:
        resp.set_cookie(cookie, "1", max_age=365 * 24 * 3600, httponly=True, samesite="lax")
    return resp


@app.post("/d/{entry_id}/unvote")
def unvote(entry_id: int, request: Request):
    entry = get_entry(entry_id)
    if not entry or entry["hidden"]:
        raise HTTPException(404, "Entry not found.")
    if entry["category"] in VENUE_CATS:
        # Vote mechanic is closed for venues (see vote above): ignore.
        if _wants_json(request):
            return JSONResponse({"ok": False, "error": "venues have no haunt vote"},
                                status_code=403)
        return RedirectResponse(f"/d/{entry_id}", status_code=303)
    cookie = f"voted_{entry_id}"
    had_vote = cookie in request.cookies
    if had_vote:
        with get_conn(DB_PATH) as conn:
            conn.execute("UPDATE entries SET votes = MAX(0, votes - 1) WHERE id = ?", (entry_id,))
            conn.commit()
        _log_engagement("unvote", entry_id)
    if _wants_json(request):
        now = get_entry(entry_id)
        resp = JSONResponse({"ok": True,
                             "votes": now["votes"] if now else entry["votes"],
                             "voted": False})
        if had_vote:
            resp.delete_cookie(cookie)
        return resp
    resp = RedirectResponse(f"/d/{entry_id}", status_code=303)
    if had_vote:
        resp.delete_cookie(cookie)
    return resp


@app.post("/d/{entry_id}/report")
def report(entry_id: int, request: Request):
    entry = get_entry(entry_id)
    if not entry or entry["hidden"]:
        raise HTTPException(404, "Entry not found.")
    with get_conn(DB_PATH) as conn:
        conn.execute("UPDATE entries SET flagged = 1 WHERE id = ?", (entry_id,))
        conn.commit()
    resp = RedirectResponse(f"/d/{entry_id}", status_code=303)
    resp.set_cookie(f"reported_{entry_id}", "1", max_age=365 * 24 * 3600,
                    httponly=True, samesite="lax")
    return resp


@app.post("/subscribe", response_class=HTMLResponse)
async def subscribe(request: Request):
    form = await request.form()
    email = form.get("email", "").strip().lower()[:120]
    location = form.get("location", "").strip()[:80] or "everywhere"
    zip_code = form.get("zip", "").strip()[:10]
    interest = (form.get("interest", "").strip()[:20] or "Halloween")
    error = None
    success = False
    if not email or "@" not in email or "." not in email.split("@")[-1]:
        error = "Please enter a valid email address."
    else:
        try:
            with get_conn(DB_PATH) as conn:
                conn.execute(
                    "CREATE TABLE IF NOT EXISTS subscribers "
                    "(id INTEGER PRIMARY KEY, email TEXT UNIQUE, location TEXT, created_at TEXT)")
                for col in ("zip", "interest"):
                    try:
                        conn.execute(f"ALTER TABLE subscribers ADD COLUMN {col} TEXT")
                    except Exception:
                        pass  # column already exists
                conn.execute(
                    "INSERT INTO subscribers (email, location, zip, interest, created_at) VALUES (?, ?, ?, ?, ?)",
                    (email, location, zip_code, interest, datetime.now(timezone.utc).isoformat()),
                )
                conn.commit()
            success = True
            # Sync to Beehiiv (one list; ZIP/town/interest ride as custom
            # fields). Double opt-in follows the publication's own setting —
            # no override is sent. Local DB stays the source of truth.
            bh_key = os.environ.get("BEEHIIV_API_KEY")
            bh_pub = os.environ.get("BEEHIIV_PUBLICATION_ID")
            if bh_key and bh_pub:
                try:
                    requests.post(
                        f"https://api.beehiiv.com/v2/publications/{bh_pub}/subscriptions",
                        headers={"Authorization": f"Bearer {bh_key}",
                                 "Content-Type": "application/json"},
                        json={"email": email, "send_welcome_email": True,
                              "custom_fields": [
                                  {"name": "TOWN", "value": location},
                                  {"name": "ZIP", "value": zip_code},
                                  {"name": "INTEREST", "value": interest},
                              ]},
                        timeout=10)
                except Exception:
                    pass  # best-effort sync
        except sqlite3.IntegrityError:
            # already subscribed — treat as success
            success = True
    # redirect back with a flag
    ref = request.headers.get("referer", "/")
    sep = "&" if "?" in ref else "?"
    return RedirectResponse(f"{ref}{sep}subscribed=1" if success else f"{ref}{sep}sub_error=1",
                            status_code=303)


TOWN_REQUESTS_TABLE_SQL = (
    "CREATE TABLE IF NOT EXISTS town_requests "
    "(id INTEGER PRIMARY KEY, email TEXT, town TEXT, state TEXT, zip TEXT, "
    "created_at TEXT)"
)


@app.post("/town-request")
async def town_request(request: Request):
    """Capture-only 'get your town on the map' requests (staged Oct 22).
    Submissions land in the town_requests table (carried by the nightly DB
    backup) and surface in /admin. No email is sent — the requests become
    the priority queue for the 20-per-town sourcing effort: towns real
    people ask for get hunted first."""
    form = await request.form()
    ref = request.headers.get("referer", "/")
    sep = "&" if "?" in ref else "?"
    # Honeypot: real visitors never see or fill this field. Bots that do get
    # a fake success and nothing is stored.
    if (form.get("website") or "").strip():
        return RedirectResponse(f"{ref}{sep}town_requested=1", status_code=303)
    email = (form.get("email") or "").strip().lower()[:120]
    town = (form.get("town") or "").strip()[:80]
    state = (form.get("state") or "").strip().upper()[:40]
    zip_code = (form.get("zip") or "").strip()[:10]
    valid = (email and "@" in email and "." in email.split("@")[-1]
             and town and state)
    if valid:
        with get_conn(DB_PATH) as conn:
            conn.execute(TOWN_REQUESTS_TABLE_SQL)
            # Cheap duplicate guard: same email + town within a day counts
            # once (double-taps, refreshes, impatient second submits).
            dupe = conn.execute(
                "SELECT 1 FROM town_requests WHERE email = ? "
                "AND LOWER(town) = LOWER(?) "
                "AND created_at >= datetime('now', '-1 day')",
                (email, town)).fetchone()
            if not dupe:
                conn.execute(
                    "INSERT INTO town_requests (email, town, state, zip, created_at) "
                    "VALUES (?, ?, ?, ?, ?)",
                    (email, town, state, zip_code,
                     datetime.now(timezone.utc).isoformat()))
                conn.commit()
        return RedirectResponse(f"{ref}{sep}town_requested=1", status_code=303)
    return RedirectResponse(f"{ref}{sep}town_req_error=1", status_code=303)


# ------------------------------------------------------------- feedback
# Visitor feedback (Dan, Oct 26): his two questions — "how can we improve
# the site?" and "what can we do to make your Halloween spookier and your
# experience here creepier?" Capture-only, same shape as town requests:
# submissions land in the feedback table (carried by the nightly DB
# backup) and surface in /admin. No email is sent.

FEEDBACK_TABLE_SQL = (
    "CREATE TABLE IF NOT EXISTS feedback "
    "(id INTEGER PRIMARY KEY, name TEXT, email TEXT, category TEXT, "
    "improve_text TEXT, spookier_text TEXT, page TEXT, created_at TEXT)"
)

FEEDBACK_CATEGORIES = {
    "site-idea": "💡 Site idea",
    "spookier": "👻 Spookier stuff",
    "bug": "🕷️ Bug report",
    "other": "🎃 Other",
}


@app.get("/feedback", response_class=HTMLResponse)
def feedback_page(request: Request):
    return templates.TemplateResponse(
        request, "feedback.html", {"site_name": SITE_NAME})


@app.post("/feedback")
async def feedback_submit(request: Request):
    form = await request.form()
    # Honeypot: real visitors never see or fill this field. Bots that do
    # get a fake success and nothing is stored (same as /town-request).
    if (form.get("website") or "").strip():
        return RedirectResponse("/feedback?sent=1", status_code=303)
    name = (form.get("name") or "").strip()[:80]
    email = (form.get("email") or "").strip().lower()[:120]
    category = (form.get("category") or "").strip()[:20]
    if category not in FEEDBACK_CATEGORIES:
        category = "other"
    improve = (form.get("improve") or "").strip()[:4000]
    spookier = (form.get("spookier") or "").strip()[:4000]
    if email and ("@" not in email or "." not in email.split("@")[-1]):
        return RedirectResponse("/feedback?error=email", status_code=303)
    if not improve and not spookier:
        # Empty submissions store nothing.
        return RedirectResponse("/feedback?error=empty", status_code=303)
    page = (form.get("page") or "").strip()[:200]
    with get_conn(DB_PATH) as conn:
        conn.execute(FEEDBACK_TABLE_SQL)
        conn.execute(
            "INSERT INTO feedback (name, email, category, improve_text, "
            "spookier_text, page, created_at) VALUES (?, ?, ?, ?, ?, ?, ?)",
            (name, email, category, improve, spookier, page,
             datetime.now(timezone.utc).isoformat()))
        conn.commit()
    return RedirectResponse("/feedback?sent=1", status_code=303)


# ------------------------------------------------------------- SMS alerts
# Capture-first (Dan, Oct 22): phone numbers are collected now and texting
# turns on when Twilio env vars land (see app/sms_alerts.py). Sending is
# NEVER faked: without credentials a signup simply stays 'captured' and the
# visitor sees the "we'll text a confirmation when alerts launch" state.

_SMS_SUBMIT_LOG: dict[str, list[float]] = {}


def _sms_rate_ok(key: str, limit: int, window_s: int = 3600) -> bool:
    """Cheap in-memory rate limit, same spirit as the town-request dupe
    guard. Per-IP submit caps + per-phone confirm-attempt caps."""
    now = time.time()
    hits = [t for t in _SMS_SUBMIT_LOG.get(key, []) if now - t < window_s]
    if len(hits) >= limit:
        _SMS_SUBMIT_LOG[key] = hits
        return False
    hits.append(now)
    _SMS_SUBMIT_LOG[key] = hits
    return True


def _flag_redirect(ref: str, **flags) -> RedirectResponse:
    """Redirect back to the referring page with our query flags swapped in
    (any stale text_alerts/sms_error params are dropped first)."""
    parts = urllib.parse.urlsplit(ref if ref.startswith("/") or "://" in ref
                                  else "/")
    q = [(k, v) for k, v in urllib.parse.parse_qsl(parts.query)
         if k not in ("text_alerts", "sms_error")]
    q += [(k, str(v)) for k, v in flags.items()]
    url = urllib.parse.urlunsplit((parts.scheme, parts.netloc, parts.path,
                                   urllib.parse.urlencode(q), ""))
    if "://" not in ref and not url.startswith("/"):
        url = "/" + url
    return RedirectResponse(url, status_code=303)


@app.post("/text-alerts")
async def text_alerts_signup(request: Request):
    form = await request.form()
    ref = request.headers.get("referer", "/")
    # Honeypot: same `website` field as the other forms. Bots get a fake
    # success and nothing is stored.
    if (form.get("website") or "").strip():
        return _flag_redirect(ref, text_alerts=1)
    ip = request.client.host if request.client else "?"
    if not _sms_rate_ok(f"signup:{ip}", 6):
        return _flag_redirect(ref, text_alerts=1)  # don't leak the limit

    phone = sms_alerts.normalize_phone(form.get("phone", ""))
    if not phone:
        return _flag_redirect(ref, sms_error="phone")
    zip_raw = re.sub(r"\D", "", form.get("zip", ""))[:5]
    town_raw = (form.get("town") or "").strip()[:60]
    town, state = sms_alerts.parse_city_state(town_raw)
    if not state:  # bare town typed without ", ST" — take state field if any
        state = (form.get("state") or "").strip().upper()[:2]
        town = town_raw
    try:
        radius = int(form.get("radius", "15"))
    except (TypeError, ValueError):
        radius = 15
    if radius not in (0, 5, 10, 15, 25, 50):
        radius = 15
    if radius == 0 and not town:
        return _flag_redirect(ref, sms_error="town")
    if radius != 0 and not zip_raw:
        return _flag_redirect(ref, sms_error="zip")
    wants_haunts = bool(form.get("want_haunts"))
    wants_events = bool(form.get("want_events"))
    interests = ("both" if wants_haunts and wants_events else
                 "haunts" if wants_haunts else
                 "events" if wants_events else "both")
    source = (form.get("source") or "")[:40] or "site"
    now = datetime.now(timezone.utc)
    code = sms_alerts.new_confirm_code()
    with get_conn(DB_PATH) as conn:
        sms_alerts.ensure_sms_tables(conn)
        # One row per phone: re-signup updates prefs and counts as fresh
        # consent (an opted-out number that signs up again on the web form
        # has explicitly opted back in — it restarts at 'captured').
        conn.execute(
            "INSERT INTO sms_subscribers (phone, zip, town, state, "
            "radius_miles, interests, consent_at, status, confirm_code, "
            "confirm_expires, source, created_at, updated_at) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, 'captured', ?, ?, ?, ?, ?) "
            "ON CONFLICT(phone) DO UPDATE SET zip=excluded.zip, "
            "town=excluded.town, state=excluded.state, "
            "radius_miles=excluded.radius_miles, "
            "interests=excluded.interests, consent_at=excluded.consent_at, "
            "status='captured', confirm_code=excluded.confirm_code, "
            "confirm_expires=excluded.confirm_expires, "
            "source=excluded.source, updated_at=excluded.updated_at",
            (phone, zip_raw or None, town or None, state or None, radius,
             interests, now.isoformat(), code,
             sms_alerts.code_expiry(now), source, now.isoformat(),
             now.isoformat()))
        sub_id = conn.execute("SELECT id FROM sms_subscribers WHERE phone = ?",
                              (phone,)).fetchone()["id"]
        conn.commit()

    if sms_alerts.twilio_configured():
        body = sms_alerts.CONFIRM_TEXT.format(code=code)
        try:
            sid = sms_alerts.send_sms(phone, body)
            with get_conn(DB_PATH) as conn:
                sms_alerts.ensure_sms_tables(conn)
                conn.execute(
                    "INSERT INTO sms_sends (subscriber_id, kind, body, "
                    "twilio_sid, status, created_at) "
                    "VALUES (?, 'confirm', ?, ?, 'sent', ?)",
                    (sub_id, body, sid,
                     datetime.now(timezone.utc).isoformat()))
                conn.commit()
            resp = _flag_redirect(ref, text_alerts="code")
            resp.set_cookie("hm_sms_pending", phone, max_age=1800, path="/",
                            httponly=True, samesite="lax")
            return resp
        except Exception:
            pass  # Twilio hiccup — signup stays captured; launch state applies
    resp = _flag_redirect(ref, text_alerts=1)
    resp.set_cookie("hm_sms_pending", phone, max_age=1800, path="/",
                    httponly=True, samesite="lax")
    return resp


@app.post("/text-alerts/confirm")
async def text_alerts_confirm(request: Request):
    form = await request.form()
    ref = request.headers.get("referer", "/")
    phone = sms_alerts.normalize_phone(
        urllib.parse.unquote(request.cookies.get("hm_sms_pending", ""))
        or form.get("phone", ""))
    code = re.sub(r"\D", "", form.get("code", ""))[:6]
    ip = request.client.host if request.client else "?"
    if not phone or not _sms_rate_ok(f"confirm:{ip}:{phone}", 10):
        return _flag_redirect(ref, text_alerts="code", sms_error="badcode")
    confirmed = False
    with get_conn(DB_PATH) as conn:
        sms_alerts.ensure_sms_tables(conn)
        row = conn.execute(
            "SELECT * FROM sms_subscribers WHERE phone = ?",
            (phone,)).fetchone()
        if row and row["status"] == "confirmed":
            confirmed = True
        elif (row and row["confirm_code"] and code
              and hmac.compare_digest(row["confirm_code"], code)
              and sms_alerts.code_still_valid(row["confirm_expires"])):
            conn.execute(
                "UPDATE sms_subscribers SET status = 'confirmed', "
                "confirm_code = NULL, confirm_expires = NULL, "
                "updated_at = ? WHERE id = ?",
                (datetime.now(timezone.utc).isoformat(), row["id"]))
            conn.commit()
            confirmed = True
    if confirmed:
        resp = _flag_redirect(ref, text_alerts="confirmed")
        resp.delete_cookie("hm_sms_pending", path="/")
        return resp
    return _flag_redirect(ref, text_alerts="code", sms_error="badcode")


@app.post("/sms/inbound")
async def sms_inbound(request: Request):
    """Twilio inbound webhook: STOP -> opted_out (never texted again),
    HELP -> help text, YES/START -> confirm/reactivate. Signature is
    enforced whenever TWILIO_AUTH_TOKEN is set."""
    form = await request.form()
    params = {k: str(v) for k, v in form.items()}
    if sms_alerts.TWILIO_TOKEN:
        proto = request.headers.get("x-forwarded-proto",
                                    request.url.scheme)
        url = f"{proto}://{request.headers.get('host', '')}{request.url.path}"
        if not sms_alerts.valid_twilio_signature(
                url, params, request.headers.get("X-Twilio-Signature", "")):
            return Response("invalid signature", status_code=403)
    phone = sms_alerts.normalize_phone(params.get("From", ""))
    word = (params.get("Body") or "").strip().upper()
    reply = ""
    if phone:
        with get_conn(DB_PATH) as conn:
            sms_alerts.ensure_sms_tables(conn)
            row = conn.execute(
                "SELECT * FROM sms_subscribers WHERE phone = ?",
                (phone,)).fetchone()
            now = datetime.now(timezone.utc).isoformat()
            if word in sms_alerts.STOP_WORDS and row:
                conn.execute(
                    "UPDATE sms_subscribers SET status = 'opted_out', "
                    "confirm_code = NULL, updated_at = ? WHERE id = ?",
                    (now, row["id"]))
                conn.commit()
            elif word in sms_alerts.YES_WORDS and row \
                    and row["status"] in ("captured", "opted_out"):
                conn.execute(
                    "UPDATE sms_subscribers SET status = 'confirmed', "
                    "confirm_code = NULL, confirm_expires = NULL, "
                    "updated_at = ? WHERE id = ?",
                    (now, row["id"]))
                conn.commit()
                reply = ("You're confirmed for HauntMap text alerts — "
                         "new haunts & events near you. Reply STOP to end.")
            elif word == "HELP":
                reply = sms_alerts.HELP_TEXT
    twiml = ('<?xml version="1.0" encoding="UTF-8"?><Response>'
             + (f"<Message>{reply}</Message>" if reply else "")
             + "</Response>")
    return Response(twiml, media_type="text/xml")


def _entries_with_views(conn, cat: str) -> list[dict]:
    """Every visible entry in a category with its detail-page view count
    attached as _views — the ranking currency Top Haunts has used since
    Dan's Oct 23 change (detail-page views, same LEFT JOIN as the
    original leaderboard query and the homepage Trending strip).
    Fortification pass 2: composed from the two TTL-cached snapshots
    (_category_rows + _views_by_id) instead of re-running the GROUP BY
    join and a full category scan on every call — the leaderboards,
    the state-Top-10 pages, the homepage hero block and the pin-page
    town rail all read through here. The conn argument is kept for
    call-site compatibility and ignored."""
    views = _views_by_id(conn)
    rows = _category_rows(cat)
    for d in rows:
        d["_views"] = views.get(d["id"], 0)
    return rows


def _rank_with_featured(entries: list[dict], limit: int) -> list[dict]:
    """Rank entries for a Top-N list, honoring editor's-pick pins.

    Base order is the site's ranking currency: detail-page views DESC,
    votes DESC, id. A pin flagged is_featured (Dan's hand-picked
    "feature as top 10" placements) is guaranteed a slot: featured pins
    lead the list (in base order among themselves) and the remaining
    slots fill from the base order. View/vote counts are NEVER altered —
    a featured pin shows its real counts beside a ⭐ Featured marker, so
    the placement is editorial and labeled as such."""
    def key(e):
        return (-(e.get("_views") or 0), -(e.get("votes") or 0), e["id"])
    featured = sorted((e for e in entries if e.get("is_featured")), key=key)
    rest = sorted((e for e in entries if not e.get("is_featured")), key=key)
    return (featured + rest)[:limit]


@app.get("/leaderboard", response_class=HTMLResponse)
def leaderboard(request: Request, cat: str = "halloween"):
    cat = cat if cat in CATEGORIES else "halloween"
    with get_conn(DB_PATH) as conn:
        # Dan, Oct 23: rank by detail-page views, same logic as the
        # homepage Trending strip — votes aren't flowing yet, so the old
        # votes-first board was effectively newest-first. Revisit votes
        # as a ranking input once they pick up.
        # Top 10 by State staging: the overall list now goes through
        # _rank_with_featured, so a flagged editor's pick is guaranteed
        # a slot here too (⭐ Featured marker; counts untouched).
        top = _rank_with_featured(_entries_with_views(conn, cat), 15)
        # Per-town Top 3 from the cached category snapshot
        # (fortification pass 2): the old loop ran one SQL query per
        # town label (~1,400 labels) on every render. The match stays
        # on the RAW town column against the derived label — preserved
        # exactly, quirk included (towns stored as full addresses match
        # no label and render an empty per-town list, as before); the
        # sort mirrors votes DESC, created_at DESC over rowid-ordered
        # rows (Python's sort is stable, like SQLite's sorter).
        base_rows = _category_rows(cat)
        per_town = []
        for t in towns(cat):
            cands = [d for d in base_rows if d["town"] == t]
            cands.sort(key=lambda d: (d["votes"] or 0, d["created_at"] or ""),
                       reverse=True)
            per_town.append({"town": t,
                             "entries": [dict(d) for d in cands[:3]]})
    return templates.TemplateResponse(request, "leaderboard.html",
        {"request": request, "top": top, "per_town": per_town,
         "cat": cat, "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI}
    )


# ------------------------------------------- Top 10 by State
#
# Dan, Oct 23: "We should make a top ten list for every state."
# One clean ranked list per state, ranked by the same currency as Top
# Haunts (detail-page views), fewer than 10 rows where a state has
# fewer than 10 pins. Editor's picks (is_featured) are guaranteed a
# slot in their state's list via _rank_with_featured and carry a
# ⭐ Featured marker — counts are never altered.
#
# Metro groups: a featured pick can belong to a metro that spans
# states (Dan's Silver Spring, MD pick is his "top ten in DMV" pick —
# DMV = DC/MD/VA, not a state). The pin is honored on its own state's
# list regardless; METRO_GROUPS additionally renders a combined metro
# Top 10 above the state sections so Dan can decide at preview
# whether metro spotlights live alongside the state lists.
METRO_GROUPS = (
    {"code": "DMV", "name": "DMV — DC · Maryland · Virginia",
     "states": ("DC", "MD", "VA")},
)


@app.get("/leaderboard/states", response_class=HTMLResponse)
def leaderboard_states(request: Request, cat: str = "halloween"):
    cat = cat if cat in CATEGORIES else "halloween"
    with get_conn(DB_PATH) as conn:
        entries = _entries_with_views(conn, cat)
    by_state: dict[str, list[dict]] = {}
    for e in entries:
        code = extract_state(e.get("town") or "")
        if not code:
            continue  # no parseable state in the town label — the pin
            # still ranks in the overall Top Haunts, just no state list
        by_state.setdefault(code, []).append(e)
    states = []
    for code, rows in by_state.items():
        states.append({
            "code": code,
            "name": US_STATE_NAMES.get(code, code),
            "count": len(rows),
            "total_views": sum(e["_views"] for e in rows),
            "entries": _rank_with_featured(rows, 10),
        })
    # Most pins first, then most views — the states with the deepest
    # lists lead the page.
    states.sort(key=lambda s: (-s["count"], -s["total_views"], s["name"]))
    metros = []
    for g in METRO_GROUPS:
        rows = [e for code in g["states"] for e in by_state.get(code, [])]
        if not rows:
            continue
        metros.append({
            "code": g["code"], "name": g["name"],
            "count": len(rows),
            "entries": _rank_with_featured(rows, 10),
        })
    return templates.TemplateResponse(request, "leaderboard_states.html",
        {"request": request, "states": states, "metros": metros,
         "cat": cat, "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI}
    )


# ------------------------------------------- Top 100 Nationwide
#
# Dan, Oct 23: a "Top 100 Nationwide" button joins the homepage VT/TV
# strip — and ships only with this real page behind it. The nation's
# top 100 pins ranked exactly like Top Haunts (detail-page views,
# votes tiebreak, via _rank_with_featured, so ⭐ Featured editor's
# picks follow the same flag logic; counts are never altered).
@app.get("/leaderboard/top-100", response_class=HTMLResponse)
def leaderboard_top100(request: Request, cat: str = "halloween"):
    cat = cat if cat in CATEGORIES else "halloween"
    with get_conn(DB_PATH) as conn:
        entries = _entries_with_views(conn, cat)
    top = _rank_with_featured(entries, 100)
    return templates.TemplateResponse(request, "leaderboard_top100.html",
        {"request": request, "top": top,
         "cat": cat, "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI}
    )


# ------------------------------------------- Auto Tour (STAGED for preview)
#
# Dan, Oct 27: "add a feature to create a tour of the top 100 and top
# ten in your area that takes some of the work out for you." One tap
# builds a ready route from the highest-ranked haunts near the visitor:
#   * Ranking currency is IDENTICAL to Top 10 by State / Top 100
#     Nationwide — _entries_with_views + _rank_with_featured (detail-
#     page views, votes tiebreak, ⭐ Featured picks guaranteed a slot;
#     counts never altered).
#   * The pool is radius-filtered around the visitor's point, and a
#     stop may enter only with coords AND a verified street address
#     (the standing address rule — a tour stop has to be routable).
#   * Stops are ordered by nearest-neighbor routing starting at the
#     VISITOR (the tour builder's Optimize button does the same greedy
#     walk, but from the first stop), tidied by a bounded 2-opt pass.
#   * A Top 100 is one ranked set presented as a ready route list,
#     grouped into "nights" of AUTO_TOUR_NIGHT_SIZE consecutive route
#     stops — 100 stops is not one drive. Each night becomes a REAL
#     tour through the existing system: the page's per-night button
#     POSTs the night's pin ids to /api/tours (the exact call the tour
#     builder's Share button makes), landing on /t/{slug} with its
#     map, Google Maps directions export, and Copy-this-tour into the
#     builder for editing. Nothing is pre-minted — no tour row exists
#     until a visitor taps. (The shared-tour cap is 50 stops, so a
#     single 100-stop tour was never an option; nights of 10 sit
#     comfortably inside it.)
AUTO_TOUR_NIGHT_SIZE = 10
# One night of driving gets a tighter 25 mi net (Dan's pick, Oct 27 —
# at 50 mi the NY-metro Top 10 routed to ~83 mi of driving); the
# Top 100 hunt gets the site's own "near" radius
# (_GEO_NEAR_RADIUS_MI = 100 mi).
AUTO_TOUR_RADIUS_MI = {10: 25.0, 100: 100.0}

# Single-state by default (Dan, Oct 27): "Let's not automate the Build
# My Tour For Me to include more than one state unless they request to
# tour multiple states at a time… they might not want to go to NYC if
# they live in NJ." A generated tour's pool is restricted to the
# visitor's own state unless the visitor opts in with the panel's
# "Include nearby states" toggle (?states=1). The visitor's state is
# resolved per location path, cheapest first: the Cloudflare geo
# signal already carries a state code; a town query usually names one
# ("Hackensack, NJ"); every other center (geolocation lat/lng, ZIP
# centroid) goes through a Nominatim reverse lookup — the same
# geocoder the town path uses forward. A state is NEVER guessed: when
# no source yields one, generation falls back to the radius-only pool
# and the page says the tour may cross state lines.
_reverse_state_cache: dict[tuple[float, float], str] = {}


def _state_code_for_point(lat: float, lng: float) -> str:
    """US state code for a point via Nominatim reverse geocoding, ''
    when the lookup fails, times out, or lands outside the US.
    Cached per ~1 km cell so repeat generations from one area cost
    one lookup."""
    key = (round(lat, 2), round(lng, 2))
    if key in _reverse_state_cache:
        return _reverse_state_cache[key]
    code = ""
    url = "https://nominatim.openstreetmap.org/reverse?" + urllib.parse.urlencode(
        {"lat": lat, "lon": lng, "format": "json", "zoom": 10})
    req = urllib.request.Request(url, headers={"User-Agent": "HauntMap/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode())
        addr = data.get("address") or {}
        if (addr.get("country_code") or "").lower() == "us":
            raw = (addr.get("state_code")
                   or addr.get("ISO3166-2-lvl4") or "").upper()
            if raw.startswith("US-"):
                raw = raw[3:]
            code = _state_code_from_region(addr.get("state") or "", raw)
    except Exception:
        code = ""
    if len(_reverse_state_cache) > 512:
        _reverse_state_cache.clear()
    _reverse_state_cache[key] = code
    return code


def _state_from_place_query(q: str) -> str:
    """State named by a town query — 'Hackensack, NJ' or 'Hackensack,
    New Jersey' — '' when the query doesn't name one."""
    parts = [p.strip() for p in (q or "").split(",") if p.strip()]
    if len(parts) >= 2:
        return _state_code_from_region(parts[-1], parts[-1])
    return ""


def _auto_tour_pool(conn, cat: str, clat: float, clng: float,
                    radius: float) -> list[dict]:
    """Eligible auto-tour stops near a point: visible pins in the
    category with coordinates AND a verified street address, within
    `radius` miles. Each returned dict is a copy carrying _views (from
    the shared ranking snapshot) and _dist (miles from the center)."""
    out = []
    for e in _entries_with_views(conn, cat):
        if e.get("lat") is None or e.get("lng") is None:
            continue
        if not (e.get("address") or "").strip():
            continue  # no verified street address — never auto-toured
        d = haversine_miles(clat, clng, e["lat"], e["lng"])
        if d <= radius:
            e = dict(e)
            e["_dist"] = d
            out.append(e)
    return out


def _auto_tour_route(stops: list[dict], clat: float,
                     clng: float) -> list[dict]:
    """Order stops as a drive starting at the visitor's point:
    nearest-neighbor, then a bounded 2-opt tidy pass (open path — the
    drive starts at the visitor and ends wherever the last stop is).
    Pure haversine on a precomputed distance matrix; n <= 100."""
    n = len(stops)
    if n < 2:
        return list(stops)
    pts = [(clat, clng)] + [(e["lat"], e["lng"]) for e in stops]
    dist = [[0.0] * (n + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        for j in range(i + 1, n + 1):
            d = haversine_miles(pts[i][0], pts[i][1], pts[j][0], pts[j][1])
            dist[i][j] = dist[j][i] = d
    # Nearest neighbor from node 0 (the visitor).
    path = [0]
    left = set(range(1, n + 1))
    while left:
        cur = path[-1]
        nxt = min(left, key=lambda k: dist[cur][k])
        path.append(nxt)
        left.discard(nxt)
    # Bounded 2-opt: reverse any segment that shortens the open path.
    for _pass in range(8):
        improved = False
        for i in range(len(path) - 2):
            a, b = path[i], path[i + 1]
            for j in range(i + 2, len(path)):
                c = path[j]
                dnode = path[j + 1] if j + 1 < len(path) else None
                old = dist[a][b] + (dist[c][dnode] if dnode is not None
                                    else 0.0)
                new = dist[a][c] + (dist[b][dnode] if dnode is not None
                                    else 0.0)
                if new < old - 1e-9:
                    path[i + 1:j + 1] = reversed(path[i + 1:j + 1])
                    improved = True
                    break
            if improved:
                break
        if not improved:
            break
    return [stops[k - 1] for k in path[1:]]


@app.get("/auto-tour", response_class=HTMLResponse)
def auto_tour(request: Request, size: int = 10, cat: str = "halloween",
              lat: str = "", lng: str = "", zip: str = "", q: str = "",
              states: str = ""):
    """Auto Tour page: the Top 10 / Top 100 near the visitor, ranked
    like the leaderboards, ordered as a route, grouped into nights.

    Center resolution mirrors the rest of the site, most explicit
    first: (1) lat/lng params (browser geolocation, like /nearby);
    (2) ZIP via the SMS engine's Census ZCTA centroids; (3) a town
    query via the same Nominatim geocoder /nearby uses; (4) the
    Cloudflare visitor-geo signal Near You uses — exact coords when
    the headers carry them, else the resolved area's anchor-town
    centroid (labeled approximate). No center at all renders the
    location picker; a wrong area is never presented as the visitor's.

    The pool is single-state by default (Dan, Oct 27): restricted to
    the visitor's own state — resolved from the CF geo state, the
    town query's named state, or a Nominatim reverse lookup on the
    center — unless the visitor opts into nearby states (?states=1,
    the panel toggle). A short in-state pool never silently expands;
    the page shows what the state has and points at the toggle.
    """
    cat = cat if cat in CATEGORIES else "halloween"
    size = 100 if size == 100 else 10
    multi = _states_opt_in(states)
    ctx = {"request": request, "size": size, "cat": cat,
           "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI,
           "need_location": False, "err": None, "nights": [],
           "center_label": "", "approx": False, "radius": 0.0,
           "total_stops": 0, "total_miles": 0.0, "pool_size": 0,
           "multi": multi, "home_state": "", "home_state_name": "",
           "wide_pool_size": 0, "center_params": {}, "route_states": []}
    center: tuple[float, float] | None = None
    label = ""
    approx = False
    center_state = ""
    center_params: dict[str, str] = {}
    if lat.strip() and lng.strip():
        try:
            la, ln = float(lat), float(lng)
            if -90 <= la <= 90 and -180 <= ln <= 180:
                center, label = (la, ln), "your location"
                center_params = {"lat": lat.strip(), "lng": lng.strip()}
        except ValueError:
            pass
    if center is None and zip.strip():
        c = sms_alerts.zip_centroid(zip)
        if c is not None:
            center, label = c, f"ZIP {zip.strip()[:5]}"
            center_params = {"zip": zip.strip()[:5]}
        else:
            ctx["err"] = f"Couldn't find ZIP {zip.strip()[:5]} — try a town instead."
    if center is None and q.strip():
        c = geocode_nominatim(q.strip())
        if c is not None:
            center, label = c, q.strip()
            center_params = {"q": q.strip()}
            center_state = _state_from_place_query(q)
        else:
            ctx["err"] = f"Couldn't find '{q.strip()}' — try a town or city name."
    if center is None:
        geo = _visitor_geo(request)
        if geo:
            center_state = geo.get("state") or ""
            if geo.get("lat") is not None and geo.get("lng") is not None:
                center = (geo["lat"], geo["lng"])
                label = (geo.get("city") or geo.get("state")
                         or "your area")
                label = f"{label} area" if label != "your area" else label
                if center_state and geo.get("city"):
                    # Same foreign-metro label rule as Near You: the
                    # header city can name the metro across the state
                    # line (Hackensack NJ resolving as "New York
                    # City") — when that city is not a town in the
                    # visitor's own state, label the tour by the
                    # visitor's resolved in-state area instead.
                    with get_conn(DB_PATH) as conn:
                        inv = _town_inventory(conn, "halloween")
                    if not any(t["state"] == center_state
                               and t["city"].lower()
                               == _smart_case_city(geo["city"]).lower()
                               for t in inv):
                        resolved = _resolve_visitor_area(
                            inv, geo, multi=multi)
                        if resolved["mode"] in ("exact", "near", "state"):
                            label = resolved["area_name"]
            elif geo.get("city") or geo.get("state"):
                with get_conn(DB_PATH) as conn:
                    inv = _town_inventory(conn, "halloween")
                resolved = _resolve_visitor_area(inv, geo, multi=multi)
                if resolved["mode"] in ("exact", "near") \
                        and resolved["chips"]:
                    anchor = next(
                        (t for t in inv
                         if t["label"] == resolved["chips"][0]["label"]),
                        None)
                    if anchor and anchor["clat"] is not None:
                        center = (anchor["clat"], anchor["clng"])
                        label = resolved["area_name"]
                        approx = True
                        if not center_state:
                            center_state = anchor.get("state") or ""
    if center is None:
        ctx["need_location"] = True
        return templates.TemplateResponse(request, "auto_tour.html", ctx)
    if not center_state:
        # Geolocation point, ZIP centroid, or a town query that named
        # no state: one reverse lookup on the center. '' = unknown —
        # the pool then stays radius-only and the page says so.
        center_state = _state_code_for_point(center[0], center[1])
    radius = AUTO_TOUR_RADIUS_MI[size]
    with get_conn(DB_PATH) as conn:
        wide_pool = _auto_tour_pool(conn, cat, center[0], center[1], radius)
    if center_state and not multi:
        pool = [e for e in wide_pool
                if extract_state(e.get("town") or "") == center_state]
    else:
        pool = wide_pool
    picked = _rank_with_featured(pool, size)
    route = _auto_tour_route(picked, center[0], center[1])
    nights = []
    for i in range(0, len(route), AUTO_TOUR_NIGHT_SIZE):
        chunk = route[i:i + AUTO_TOUR_NIGHT_SIZE]
        miles = 0.0
        prev = center
        for e in chunk:
            leg = haversine_miles(prev[0], prev[1], e["lat"], e["lng"])
            e["_leg"] = leg
            miles += leg
            prev = (e["lat"], e["lng"])
        nights.append({
            "num": len(nights) + 1,
            "stops": chunk,
            "miles": miles,
            "ids": [e["id"] for e in chunk],
            "title": (f"Top {len(route)} near {label} — Night "
                      f"{len(nights) + 1} of "
                      f"{(len(route) + AUTO_TOUR_NIGHT_SIZE - 1) // AUTO_TOUR_NIGHT_SIZE}"
                      if size == 100 else
                      f"Top {len(route)} near {label} — Auto Tour"),
        })
    ctx.update({"nights": nights, "center_label": label,
                "approx": approx, "radius": radius,
                "total_stops": len(route),
                "total_miles": sum(n["miles"] for n in nights),
                "pool_size": len(pool),
                "home_state": center_state,
                "home_state_name": US_STATE_NAMES.get(center_state,
                                                      center_state),
                "wide_pool_size": len(wide_pool),
                "center_params": center_params,
                "route_states": sorted(
                    {extract_state(e.get("town") or "") for e in route}
                    - {""})})
    return templates.TemplateResponse(request, "auto_tour.html", ctx)


# ------------------------------------------------- Haunt Passport (Wave 4, Item 4)
#
# The collection loop, surfaced. A pin-page visit marks the pin seen in
# the visitor's localStorage (hm_seen, see base.html); /passport turns
# that device-local set into per-town progress. Counting mirrors the
# town feed EXACTLY: the denominators are the _towns_with_counts /
# town_page universe — visible (hidden = 0) halloween pins grouped by
# the extract_city_state town label — because those are the counts a
# visitor sees on /towns/{slug}, and detail()'s own seen-strip counts
# the same label+category set for a halloween pin. Towns whose pins
# carry no parseable "City, ST" label never appear in the town feed,
# so they are excluded here too (same rule as _towns_with_counts).
# Non-halloween pins (events, stores, …) are not part of the town feed
# and do not count toward a town — documented in item4 NOTES.

def _passport_towns(conn=None) -> list[dict]:
    """[{town, town_label, total, url, slug, ids}] for the passport.

    `ids` rides along beyond the spec'd fields: the progress itself is
    computed client-side from the visitor's seen set, which is a bare
    list of pin ids, so the client needs each town's id list to count
    how many of them were seen. `town` and `town_label` are both the
    canonical extract_city_state label (the key the town feed groups
    by, and the label every card displays). TTL-cached +
    background-refreshed (fortification pass 2); callers get copies.
    The conn argument is kept for call-site compatibility."""
    def build():
        grouped: dict[str, list[int]] = {}
        with get_conn(DB_PATH) as c:
            rows = c.execute(
                "SELECT id, town FROM entries "
                "WHERE hidden = 0 AND category = 'halloween' ORDER BY id").fetchall()
        for r in rows:
            label = extract_city_state(r["town"] or "")
            if not label:
                continue
            grouped.setdefault(label, []).append(r["id"])
        out = []
        for label in sorted(grouped):
            slug = _town_slug(label)
            out.append({"town": label, "town_label": label,
                        "total": len(grouped[label]),
                        "url": f"/towns/{slug}", "slug": slug,
                        "ids": grouped[label]})
        return out
    base = _ttl_cached("passport:towns", build)
    return [{**t, "ids": list(t["ids"])} for t in base]


@app.get("/api/passport-data")
def api_passport_data():
    """Per-town passport denominators + pin ids, as one JSON list.
    TTL-cached server-side (fortification pass 2) on top of the
    Cache-Control below, which lets browsers / the CDN reuse it
    briefly instead of recomputing on every homepage load, since the
    homepage chip fetches it too."""
    data = _passport_towns()
    resp = JSONResponse(data)
    resp.headers["Cache-Control"] = "public, max-age=300"
    return resp


# ------------------------------------------------- Passport → account (#11)
#
# The passport above is deliberately account-free: hm_seen never
# leaves the visitor's device. HauntSocial profiles, though, want the
# collection as social proof (Dan's pick #11, Oct 25) — and a member's
# stamps can only be real if the account actually holds them. So a
# SIGNED-IN member's browser union-merges its device set into
# passport_stamps via the endpoint below (see the member-only script
# in base.html). Anonymous traffic is untouched: no endpoint call, no
# rows, no behavior change.

# One sync payload's cap. The client itself keeps at most 3000 ids in
# hm_seen (base.html), so a longer list is never legitimate.
PASSPORT_SYNC_MAX = 3000
# Stamps shown on the profile block (the total counts all of them).
PASSPORT_PROFILE_RECENT = 6


@app.post("/api/passport/sync")
async def api_passport_sync(request: Request):
    """Union-merge a member's device passport set into their account.

    Body: {ids: [...]} — the client's current hm_seen list. Ids are
    de-duped, capped at PASSPORT_SYNC_MAX, and validated against
    `entries` in ONE query (bogus ids drop out); the merge itself is a
    single executemany of INSERT OR IGNORE in one transaction — never
    a delete, so devices union instead of overwriting each other.
    Requires a member session: anonymous callers get a 401 and nothing
    is written. Returns {ok, added, total} for the account."""
    member = current_member(request)
    if member is None:
        return JSONResponse(
            {"error": "Sign in to sync your passport."}, status_code=401)
    try:
        data = await request.json()
    except Exception:
        data = {}
    raw = data.get("ids") if isinstance(data, dict) else None
    ids: list[int] = []
    seen_ids: set[int] = set()
    for x in raw or []:
        try:
            i = int(x)
        except (TypeError, ValueError):
            continue
        if i > 0 and i not in seen_ids:
            seen_ids.add(i)
            ids.append(i)
    ids = ids[:PASSPORT_SYNC_MAX]
    now = datetime.now(timezone.utc).isoformat()
    with get_conn(DB_PATH) as conn:
        before = conn.execute(
            "SELECT COUNT(*) AS n FROM passport_stamps WHERE user_id = ?",
            (member["id"],)).fetchone()["n"]
        if ids:
            ph = ",".join("?" * len(ids))
            valid = {r["id"] for r in conn.execute(
                f"SELECT id FROM entries WHERE id IN ({ph})", ids)}
            rows = [(member["id"], i, now) for i in ids if i in valid]
            if rows:
                conn.executemany(
                    "INSERT OR IGNORE INTO passport_stamps "
                    "(user_id, entry_id, stamped_at) VALUES (?, ?, ?)",
                    rows)
                conn.commit()
        total = conn.execute(
            "SELECT COUNT(*) AS n FROM passport_stamps WHERE user_id = ?",
            (member["id"],)).fetchone()["n"]
    return JSONResponse({"ok": True, "added": total - before, "total": total})


def _passport_stamps_view(conn, user_id: int) -> dict | None:
    """Profile Haunt Passport block data for a member: total stamp
    count + the most recent few (title/town for the link list), or
    None when the member has no visible stamps (block hidden). Only
    visible pins count — a stamp on a since-hidden pin is not social
    proof and must not leak the pin's title."""
    rows = conn.execute(
        "SELECT s.entry_id, e.title, e.town FROM passport_stamps s "
        "JOIN entries e ON e.id = s.entry_id "
        "WHERE s.user_id = ? AND e.hidden = 0 "
        "ORDER BY s.stamped_at DESC, s.entry_id DESC LIMIT ?",
        (user_id, PASSPORT_PROFILE_RECENT)).fetchall()
    if not rows:
        return None
    total = conn.execute(
        "SELECT COUNT(*) AS n FROM passport_stamps s "
        "JOIN entries e ON e.id = s.entry_id "
        "WHERE s.user_id = ? AND e.hidden = 0",
        (user_id,)).fetchone()["n"]
    return {"total": total,
            "recent": [{"entry_id": r["entry_id"], "title": r["title"],
                        "town": r["town"]} for r in rows]}


@app.get("/passport", response_class=HTMLResponse)
def passport_page(request: Request):
    """Haunt Passport page. The shell is server-rendered; the progress
    itself is rendered client-side from hm_seen + /api/passport-data
    (the seen set never leaves the visitor's device — no accounts)."""
    return templates.TemplateResponse(request, "passport.html", {})


# ---------------------------------------------------------------- town pages

def _town_slug(label: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", label.lower()).strip("-")


def _towns_with_counts(category: str = "halloween") -> list[dict]:
    """[{label, slug, count}] per town in a category. TTL-cached +
    background-refreshed (fortification pass 2): it full-scans the
    category's town strings and feeds /towns and the homepage's
    place-tabs counter."""
    def build():
        with get_conn(DB_PATH) as conn:
            rows = conn.execute(
                "SELECT town FROM entries WHERE hidden = 0 AND category = ?",
                (category,),
            ).fetchall()
        counts: dict[str, int] = {}
        for r in rows:
            label = extract_city_state(r["town"] or "")
            if label:
                counts[label] = counts.get(label, 0) + 1
        if category == "halloween":
            # Canada opens (Dan, Oct 27): a town whose only pins are
            # events (first case: Abbotsford, BC — Maan Farms' Halloween
            # Fright Festival) still earns a /towns listing and a town
            # page. Towns that already have halloween pins keep their
            # existing counts untouched.
            with get_conn(DB_PATH) as conn:
                erows = conn.execute(
                    "SELECT town FROM entries WHERE hidden = 0 "
                    "AND category = 'events'").fetchall()
            ecounts: dict[str, int] = {}
            for r in erows:
                label = extract_city_state(r["town"] or "")
                if label:
                    ecounts[label] = ecounts.get(label, 0) + 1
            for label, c in ecounts.items():
                counts.setdefault(label, c)
        return sorted(
            ({"label": l, "slug": _town_slug(l), "count": c}
             for l, c in counts.items()),
            key=lambda x: x["label"],
        )
    return [dict(t) for t in _ttl_cached(f"towncounts:{category}", build)]


@app.get("/towns", response_class=HTMLResponse)
def towns_index(request: Request):
    return templates.TemplateResponse(
        request, "towns.html",
        {"towns_list": _towns_with_counts(), "site_name": SITE_NAME},
    )


def _entry_has_video(e: dict) -> bool:
    """Footage predicate matching the feed's 'Has video' filter: a TikTok URL
    or an uploaded video file."""
    if (e.get("tiktok_url") or "").strip():
        return True
    if e.get("media_type") == "video":
        return True
    return (e.get("media_path") or "").lower().endswith((".mp4", ".webm", ".mov"))


@app.get("/towns/{slug}", response_class=HTMLResponse)
def town_page(request: Request, slug: str):
    label = None
    for t in _towns_with_counts():
        if t["slug"] == slug:
            label = t["label"]
            break
    if label is None:
        return RedirectResponse("/towns", status_code=303)
    # Rows from the shared _category_rows snapshot (fortification
    # pass 2) instead of a per-render full-category scan + row_to_dict
    # pass. The feed order (Dan, Oct 23: hand-picked pins first —
    # newest hand-picked first — then newest-first; the town page has
    # no sort control, so this IS its default view) is the old SQL
    # ORDER BY applied as a Python sort over the snapshot rows before
    # the town filter, exactly as the SQL ordered-then-filtered.
    rows = _category_rows("halloween")
    rows.sort(key=lambda e: (e["is_handpicked"] or 0,
                             e["created_at"] or "", e["id"]),
              reverse=True)
    entries = [e for e in rows if e["town_label"] == label]
    if not entries:
        # Events-only towns (Canada opening, Oct 27): the town resolved
        # via its event pins, so list those — same feed order as above.
        erows = _category_rows("events")
        erows.sort(key=lambda e: (e["is_handpicked"] or 0,
                                  e["created_at"] or "", e["id"]),
                   reverse=True)
        entries = [e for e in erows if e["town_label"] == label]
    # Item 7: town-page cards show all-time view counts (one grouped query).
    with get_conn(DB_PATH) as conn:
        _attach_views(conn, entries)
    # Retention Wave 3, Item 5: the "Tonight" strip under the town header
    # — this town is the anchor; displays lit = its halloween pins (the
    # entries list itself), events on = parsed events in this town.
    tstrip = _tonight_strip(label, len(entries))
    return templates.TemplateResponse(
        request, "town.html",
        {"label": label, "entries": entries, "site_name": SITE_NAME,
         "tstrip": tstrip},
    )


@app.get("/sitemap.xml")
def sitemap():
    base = "https://gethauntmap.com"
    urls = ["/", "/map", "/nearby", "/tour", "/diy", "/diy-costumes", "/games", "/games/ghost-maze", "/leaderboard", "/leaderboard/states", "/leaderboard/top-100",
            "/towns", "/passport", "/daily", "/advertise", "/media-kit", "/about", "/hauntsocial", "/chat", "/costume-contest", "/trivia", "/haunt-or-not", "/fan-art",
            "/restaurhaunts"]
    for t in _towns_with_counts():
        urls.append(f"/towns/{t['slug']}")
    body = ['<?xml version="1.0" encoding="UTF-8"?>',
            '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">']
    for u in urls:
        body.append(f"<url><loc>{base}{u}</loc></url>")
    body.append("</urlset>")
    return Response("\n".join(body), media_type="application/xml")


# ---------------------------------------------------------------- advertise

# Business sponsor packages (the original pitched tiers — quotes honored).
BUSINESS_PACKAGES = [
    {"id": "featured", "name": "Featured", "price": 250,
     "stripe_link": "https://buy.stripe.com/28EfZg2FW7H0d1SeCybbG00",
     "blurb": "Your business in front of local Halloween haunters.",
     "features": ["Logo + link in the Featured Sponsors row on the homepage",
                  "Featured pin for your location",
                  "A full year of sponsorship — site, social media, and newsletter for 12 months from purchase, through the same holiday next year"]},
    {"id": "premium", "name": "Premium", "price": 500,
     "stripe_link": "https://buy.stripe.com/7sY7sK3K05ySge49iebbG01",
     "blurb": "Homepage plus the weekly email — for a full year.",
     "features": ["Everything in Featured",
                  "A full year of sponsorship — site, social media, and newsletter for 12 months from purchase, through the same holiday next year",
                  "Sponsor spot in the weekly Haunt Weekly / Jolly Weekly email",
                  "Logo placement on town pages",
                  "Monthly click report"]},
    {"id": "title", "name": "Title Sponsor", "price": 1000,
     "stripe_link": "https://buy.stripe.com/4gM7sK3K0bXg7Hy8eabbG02",
     "blurb": "The top spot, everywhere.",
     "features": ["Everything in Premium",
                  "Top banner placement sitewide",
                  "Featured story in the weekly email",
                  "Social media shoutout",
                  "Monthly click report"]},
]

# Homeowner ladder — the Founding-Sponsor Rates, for private home displays.
SPONSOR_PACKAGES = [
    {"id": "tour_fuel", "name": "Tour Fuel Listing", "price": 49, "price_both": 79,
     "blurb": "A stop on the route — coffee, food and shops near the haunts.",
     "features": ["Listed as a \u201cTour Fuel\u201d stop on town pages and custom tours",
                  "Logo + link on your town's page",
                  "Runs the full season you pick"]},
    {"id": "town_featured", "name": "Town Featured", "price": 79, "price_both": 129,
     "blurb": "Own your town's page.",
     "features": ["Everything in Tour Fuel Listing",
                  "Featured placement at the top of your town's page",
                  "Featured pin for your location",
                  "Monthly click report"]},
    {"id": "sitewide_featured", "name": "Sitewide Featured", "price": 149, "price_both": 249,
     "blurb": "The top spot, everywhere on the map.",
     "features": ["Everything in Town Featured",
                  "Featured sponsor banner on the homepage, sitewide",
                  "Sponsor spot in the Haunt Weekly / Jolly Weekly email",
                  "Monthly click report"]},
]

SPONSOR_ORDER_GROUPS = [
    {"label": "Business — Sponsor Packages", "options": [
        {"id": "featured", "label": "Business — Featured — $250"},
        {"id": "premium", "label": "Business — Premium — $500"},
        {"id": "title", "label": "Business — Title Sponsor — $1,000"},
    ]},
    {"label": "Homeowner — Feature Your Display", "options": [
        {"id": "tour_fuel", "label": "Homeowner — Tour Fuel Listing — $49 (one season)"},
        {"id": "tour_fuel_both", "label": "Homeowner — Tour Fuel Listing — $79 (both seasons)"},
        {"id": "town_featured", "label": "Homeowner — Town Featured — $79 (one season)"},
        {"id": "town_featured_both", "label": "Homeowner — Town Featured — $129 (both seasons)"},
        {"id": "sitewide_featured", "label": "Homeowner — Sitewide Featured — $149 (one season)"},
        {"id": "sitewide_featured_both", "label": "Homeowner — Sitewide Featured — $249 (both seasons)"},
    ]},
]

SPONSOR_ORDER_OPTIONS = [o for g in SPONSOR_ORDER_GROUPS for o in g["options"]]


@app.get("/advertise", response_class=HTMLResponse)
def advertise(request: Request):
    today_d = datetime.now(timezone.utc).date()
    stats = {"today": 0, "week": 0, "pins": 0, "towns": 0}
    # Sponsor-facing counts are the SAME human-only numbers the media
    # kit quotes, sourced from the shared _mk_* helpers (Oct 27, 2026
    # fix): this handler used to run its own COUNT(DISTINCT sid) over
    # ALL page_views with no machine-path exclusion, so /healthz pings
    # (each carrying its own sid) inflated "visitors today" ~3x
    # (17,478 shown vs the kit's 5,810) and its rolling-7x24h "week"
    # window (199,644) disagreed with the kit's 7-calendar-day window
    # (104,651). One computation, both pages, never drift again.
    try:
        vis = _mk_visitors(today_d)
        stats["today"] = vis["today"]
        stats["week"] = vis["week"]
    except Exception:
        pass
    try:
        stats["pins"] = sum(_category_counts().values())
        stats["towns"] = _mk_geo()["town_count"]
    except Exception:
        pass
    with get_conn(DB_PATH) as conn:
        sponsors = [dict(r) for r in conn.execute(
            "SELECT * FROM sponsors WHERE is_active = 1 ORDER BY "
            "CASE tier WHEN 'title' THEN 0 WHEN 'premium' THEN 1 ELSE 2 END LIMIT 1").fetchall()]
    pkg = request.query_params.get("pkg", "")
    if pkg not in {o["id"] for o in SPONSOR_ORDER_OPTIONS}:
        pkg = ""
    return templates.TemplateResponse(
        request, "advertise.html",
        {"packages": SPONSOR_PACKAGES, "business_packages": BUSINESS_PACKAGES,
         "stats": stats, "example": sponsors[0] if sponsors else None,
         "towns": towns("halloween"), "site_name": SITE_NAME,
         "order_options": SPONSOR_ORDER_OPTIONS, "order_groups": SPONSOR_ORDER_GROUPS,
         "selected_pkg": pkg,
         "ordered": request.query_params.get("ordered")},
    )


@app.post("/advertise/order")
async def advertise_order(
    business_name: str = Form(...),
    contact_name: str = Form(""),
    email: str = Form(...),
    package: str = Form("tour_fuel"),
    town: str = Form(""),
    website: str = Form(""),
    logo: UploadFile = File(None),
):
    logo_rel = None
    if logo and logo.filename:
        ext = safe_ext(logo.filename)
        if ext in PHOTO_EXTS:
            try:
                tmp = save_upload(logo, MAX_PHOTO_BYTES)
                name = uuid.uuid4().hex
                logo_rel = f"{name}{ext}"
                shutil.move(tmp, UPLOAD_DIR / logo_rel)
            except ValueError:
                logo_rel = None
    with get_conn(DB_PATH) as conn:
        conn.execute(
            "CREATE TABLE IF NOT EXISTS sponsor_orders "
            "(id INTEGER PRIMARY KEY, business_name TEXT, contact_name TEXT, email TEXT, "
            "package TEXT, town TEXT, website TEXT, logo_path TEXT, status TEXT, created_at TEXT)")
        conn.execute(
            "INSERT INTO sponsor_orders (business_name, contact_name, email, package, town, website, logo_path, status, created_at) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, 'new', ?)",
            (business_name.strip()[:120], contact_name.strip()[:80], email.strip().lower()[:120],
             package, town.strip()[:80], website.strip()[:200], logo_rel,
             datetime.now(timezone.utc).isoformat()),
        )
    return RedirectResponse("/advertise?ordered=1", status_code=303)


# ---------------------------------------------------------------- media kit

MEDIA_KIT_CATEGORY_LABELS = [
    ("halloween", "Halloween displays"),
    ("christmas", "Christmas displays (Jolly Map)"),
    ("haunted_houses", "Haunted houses"),
    ("events", "Events"),
    ("halloween_stores", "Halloween stores"),
    ("restaurants", "Restaurhaunts"),
    ("coffee", "Coffee & cafes"),
    ("shops", "Shops"),
    ("parks", "Parks"),
    ("hotels", "Hotels"),
    ("ice_cream", "Ice Cream"),
    ("live", "Live"),
]

MEDIA_KIT_GAMES = ["The Halloween Arcade (8 free games)", "Ghost Maze", "Haunt or Not", "Haunt Bracket", "Scare-O-Meter", "Daily Halloween Trivia", "Costume Contest"]


@app.get("/about", response_class=HTMLResponse)
def about(request: Request):
    # The mission text lives here now (moved off the homepage hero, Dan
    # Oct 22) — its coverage numbers are computed live, same as /media-kit.
    stats = {"total_pins": 0, "town_count": 0, "state_count": 0, "has_dc": False}
    with get_conn(DB_PATH) as conn:
        stats["total_pins"] = conn.execute(
            "SELECT COUNT(*) FROM entries WHERE hidden = 0").fetchone()[0]
        town_rows = conn.execute(
            "SELECT DISTINCT town FROM entries WHERE hidden = 0").fetchall()
    labels: set[str] = set()
    state_set: set[str] = set()
    for r in town_rows:
        label = extract_city_state(r["town"] or "")
        if label:
            labels.add(label)
        st = extract_state(r["town"] or "")
        if st:
            state_set.add(st)
    stats["town_count"] = len(labels)
    stats["state_count"] = len(state_set - {"DC"})
    stats["has_dc"] = "DC" in state_set
    return templates.TemplateResponse(
        request, "about.html", {"stats": stats, "site_name": SITE_NAME},
    )


@app.get("/embed-test", response_class=HTMLResponse)
def embed_test(request: Request):
    # Unlisted diagnostic (Oct 23): TikTok embeds load their player on
    # Dan's laptop but never play, on every surface and in both Safari
    # and Chrome, while tiktok.com itself plays once he logs in — the
    # leading theory is the third-party embed frame can't reach a
    # TikTok session. This page shows the SAME Scare-O-Meter rail video
    # (7699668838786370847) three ways — A: the production facade ->
    # hmLoadTikTok swap, B: a plain embed/v2 iframe, C: TikTok's raw
    # share-sheet blockquote + embed.js — so Dan can tap each on the
    # laptop and report which (if any) plays; that result picks the
    # production fix. No nav links anywhere; template carries noindex.
    return templates.TemplateResponse(
        request, "embed_test.html", {"site_name": SITE_NAME},
    )


# ---------------------------------------------------------------- music
# /music (Dan, Oct 22): the site's music room — verified Spotify playlists,
# YouTube classics and the artists who own Halloween. Every ID and URL below
# was verified via Spotify / YouTube oEmbed on 2026-10-22 (title + author
# match, embeddable) — never add a link here without the same check.
MUSIC_SPOTIFY_PLAYLISTS = [
    {"id": "6UkHy4ryQKNsBtnwoIbymc",
     "title": "The Only Halloween Playlist You'll Ever Need",
     "blurb": "The big one — Thriller, Ghostbusters, Monster Mash and dozens "
              "more party staples in one list."},
    {"id": "3GR3i1bykOapAJEncHgWnj",
     "title": "24-Hour Halloween Party Mix",
     "blurb": "A full day of Halloween party tracks — set it running before "
              "the first knock at the door."},
    {"id": "58HhYIGD0vWO54G9ftX04q",
     "title": "Synthwave Halloween — Horror Synth",
     "blurb": "Dark synth and horror-score energy for the drive between "
              "haunts."},
]
# Live radio for /music (Dan, Oct 26): iHeartRadio's official embed
# player — the ?embed=true&keyid=EditorialPlayer iframe iHeart itself
# ships in its station pages' oEmbed markup ("Embed widget"); the
# station pages send no frame-blocking headers. Every slug below was
# test-rendered in that embed on 2026-10-26 and showed live now-playing
# data — never add a station here without the same check. Halloween
# first, then the big New York iHeart flagships. Radio Garden refuses
# embedding in-app ("Embedding Not Allowed", verified 2026-10-26), so
# it rides as a link-out card in the template instead.
MUSIC_RADIO_IHEART = [
    {"slug": "halloween-radio-7001", "name": "Halloween Radio",
     "format": "Halloween Hits · Commercial-Free", "halloween": True,
     "lead": True,
     "blurb": "iHeart's Halloween flagship — Thriller, Ghostbusters, "
              "Monster Mash and the rest of the canon, no commercials."},
    {"slug": "haunted-house-radio-9163", "name": "Haunted House Radio",
     "format": "Spooky Halloween Sounds in 3D", "halloween": True,
     "blurb": "Pure atmosphere — eerie soundscapes for the porch "
              "speaker. Point it at the sidewalk and the display "
              "comes alive."},
    {"slug": "trick-or-treat-radio-11287", "name": "Trick or Treat Radio",
     "format": "Kids' Halloween Music · Commercial-Free",
     "halloween": True,
     "blurb": "The family lane — sing-along Halloween hits for the "
              "littlest goblins."},
    {"slug": "z100-1469", "name": "Z100",
     "format": "New York's #1 Hit Music Station",
     "blurb": "Today's biggest pop, live from New York."},
    {"slug": "1035-ktu-1473", "name": "103.5 KTU",
     "format": "The Beat of New York",
     "blurb": "Dance, throwbacks and party starters — the KTU sound."},
    {"slug": "q1043-1465", "name": "Q104.3",
     "format": "New York's Rock Station",
     "blurb": "Classic rock that really rocks, all day."},
    {"slug": "1067-lite-fm-1477", "name": "106.7 Lite FM",
     "format": "New York's Best Variety",
     "blurb": "The softer side of the dial — workday variety."},
]
# EDM Channels (Dan, Oct 26): the major EDM YouTube channels, one card
# each, leading the /music page. Every ID verified via YouTube oEmbed on
# 2026-10-26 (title + author match, embeddable). Spinnin's pick is the
# label's official 24/7 live radio — its watch page confirmed isLiveNow
# at verification time. The rest are each channel's flagship mix or
# defining upload (Monstercat's Best of 2025 album mix, NCS's 3-hour
# 10 Year MIX, Proximity's Decade Mix, Sheepy's Taking You Higher mix,
# UKF's On Air live session, Revealed Radio's best-of episode; Trap
# Nation posts premieres, not mixes, so its card is the Lucian remix —
# the upload that built the channel). Selected. and Musical Freedom
# were dropped: no verifiable official flagship mix on either channel.
MUSIC_EDM_CHANNELS = [
    {"name": "Spinnin' Records", "id": "xf9Ejt4OmWQ",
     "title": "Spinnin' Records | 24/7 Live Radio | Best Dance Music",
     "blurb": "The Dutch giant's own radio — big-room, house and dance, "
              "live around the clock.",
     "meta": "🔴 LIVE · 24/7 Live Radio"},
    {"name": "Monstercat", "id": "JVYDN3PmOG4",
     "title": "Monstercat - Best of 2025 [Album Mix]",
     "blurb": "The label that launched a thousand bass drops — the "
              "year's heaviest Monstercat releases in one album mix.",
     "meta": "Best of 2025 [Album Mix] · 1:33:39"},
    {"name": "NCS (NoCopyrightSounds)", "id": "yUXJjIvhZz8",
     "title": "NCS 10 Year MIX - 3 Hours | NCS - Copyright Free Music",
     "blurb": "The copyright-free giants — three straight hours of the "
              "biggest NCS releases ever, back to back.",
     "meta": "10 Year MIX · 2:59:55"},
    {"name": "Trap Nation", "id": "DArzZ3RvejU",
     "title": "Alessia Cara - Here (Lucian Remix)",
     "blurb": "YouTube's trap tastemakers — the Lucian remix of "
              "“Here” is the upload that built the Nation.",
     "meta": "Alessia Cara — Here (Lucian Remix)"},
    {"name": "UKF", "id": "CxB1AO6AcmA",
     "title": "Shift K3Y with Live Orchestra London Mozart Players - "
              "UKF On Air",
     "blurb": "The UK bass institution — UKF On Air takes Shift K3Y "
              "into the concert hall with a live orchestra.",
     "meta": "UKF On Air · live session"},
    {"name": "Proximity", "id": "gnV-8pkILF0",
     "title": "Proximity - Best EDM of 2010-2019 (Decade Mix)",
     "blurb": "The curator channel that broke a generation of EDM — "
              "the best of a whole decade in one ride.",
     "meta": "Decade Mix · 2:17:03"},
    {"name": "MrSuicideSheep", "id": "GN5fRaKla5Y",
     "title": "'Taking You Higher Pt. 5' (Progressive House Mix)",
     "blurb": "The sheep that soundtracked a million late nights — "
              "his beloved progressive house mix series, part five.",
     "meta": "Taking You Higher Pt. 5 · Progressive House Mix"},
    {"name": "Revealed Recordings", "id": "OvfL__kKcWQ",
     "title": "Revealed Radio 100 - Best of Revealed Radio",
     "blurb": "Hardwell's label — the best-of episode of Revealed "
              "Radio, its long-running weekly show.",
     "meta": "Revealed Radio 100 · 56:20"},
]
# Hip Hop Stations (Dan, Oct 26): hip hop's home bases, directly under
# the EDM Channels on /music, same card pattern. Every ID verified via
# YouTube oEmbed on 2026-10-26 (title + author match, embeddable,
# thumbnail 200). Lofi Girl's pick is her genuine 24/7 radio — its
# watch page confirmed isLiveNow at verification time. The Jazz Hop
# Café is a net radio station + label; its card is the Café's one-hour
# Halloween lofi session. The rest are each institution's defining
# session: Sway's 5 Fingers of Death, On The Radar's Drake & Central
# Cee freestyle, XXL's 2016 Freshman Cypher, Mass Appeal's Rhythm
# Roulette. Chillhop Music was dropped: its 24/7 radio streams check
# out dead today (ended recordings, an "offline" placeholder, a 404) —
# no playable live stream to point at.
MUSIC_HIPHOP_STATIONS = [
    {"name": "Lofi Girl", "id": "jfKfPfyJRdk",
     "title": "lofi hip hop radio 📚 beats to relax/study to",
     "blurb": "The stream that never sleeps — the lofi girl studies "
              "on and the beats roll around the clock.",
     "meta": "🔴 LIVE · 24/7 lofi hip hop radio"},
    {"name": "The Jazz Hop Café", "id": "0u6KjmyGzO8",
     "title": "Cabin in the Woods 🏚️ Halloween Lofi Vibes",
     "blurb": "A net radio station and record label brewing jazz-hop "
              "— this session was poured for Halloween: a cabin in "
              "the woods, lofi on the turntable.",
     "meta": "Halloween lofi session · 1:00:00"},
    {"name": "Sway's Universe", "id": "AHwZBYCwxPY",
     "title": "Tory Lanez Kills The 5 Fingers of Death (9 Minute "
              "Freestyle) | Sway's Universe",
     "blurb": "Sway in the Morning's proving ground — nine straight "
              "minutes of Tory Lanez over five beats, no safety net.",
     "meta": "5 Fingers of Death · 11:47"},
    {"name": "On The Radar Radio", "id": "cfX1QlfxTBI",
     "title": "The Drake & Central Cee \"On The Radar\" Freestyle",
     "blurb": "The freestyle platform of the moment — Drake and "
              "Central Cee trading bars in the OTR studio.",
     "meta": "Drake & Central Cee freestyle · 4:54"},
    {"name": "XXL", "id": "U_IbIMUbh-k",
     "title": "Kodak Black, 21 Savage, Lil Uzi Vert, Lil Yachty & "
              "Denzel Curry 2016 XXL Freshman Cypher",
     "blurb": "The cypher that launched a generation — the 2016 "
              "Freshman class, one four-minute pass, no edits.",
     "meta": "2016 Freshman Cypher · 4:13"},
    {"name": "Mass Appeal", "id": "R4uZ8S8HBKg",
     "title": "Rhythm Roulette: Havoc | Mass Appeal",
     "blurb": "Nas's label's beat-making ritual — Havoc of Mobb Deep "
              "draws three records blind and builds a beat from them.",
     "meta": "Rhythm Roulette · Havoc · 7:01"},
]
# Top-of-page featured set (Dan, Oct 23): his friends' ZombieSquad mix on
# the Dead On Pictures channel, featured at the top of /music by request.
# Verified via yt-dlp 2026-10-23: public, playable_in_embed, maxres thumb.
# Dan, Oct 27: the Featured Set section itself now sits at the very top of
# /music (above the EDM Channels), as THE feature of the page.
MUSIC_SPOTLIGHT = {
    "id": "MlgxFvrCgoA",
    "title": "ZombieSquad EDM Mix Session | 20261023 | EDM - Dance - House",
    "channel": "Dead On Pictures",
    "meta": "Full-length set · 2:13:03",
}
# Directly below the ZombieSquad feature (Dan, Oct 27): the Halloween
# future bass mix he sent the same morning — moved out of the DJ Sets
# grid (where it sat last) into the featured flow, as the next entry a
# visitor sees. oEmbed-verified 2026-10-27 (title + channel, embeddable).
MUSIC_SPOTLIGHT_NEXT = {
    "id": "WOGat2B7Vak",
    "title": "Spooky Vibes (2026) // Future Bass Mix - EDM Vibes Collection",
    "channel": "Timothy Caldwell",
    "meta": "A future bass Halloween mix from the EDM Vibes Collection",
}
MUSIC_YOUTUBE_FEATURED = {
    "id": "sOnqjkJTMaA",
    "title": "Michael Jackson — Thriller (Official 4K Video)",
    "channel": "michaeljacksonVEVO",
}
MUSIC_YOUTUBE_GRID = [
    {"id": "Fe93CLbHjxQ", "title": "Ray Parker Jr. — Ghostbusters",
     "channel": "RayParkerJuniorVEVO"},
    {"id": "ZVuToMilP0A",
     "title": "The Citizens of Halloween — This Is Halloween",
     "channel": "DisneyMusicVEVO"},
    {"id": "EqQuihD0hoI", "title": "Rob Zombie — Dragula",
     "channel": "RobZombieVEVO"},
    {"id": "NF69rFld9zQ",
     "title": "Bobby \"Boris\" Pickett — Monster Mash (Official Lyric Video)",
     "channel": "Radial by The Orchard"},
    {"id": "E1mU6h4Xdxc", "title": "Rihanna — Disturbia",
     "channel": "RihannaVEVO"},
]
# Legendary live Halloween performances (Dan's picks, Oct 23). Every ID
# re-verified via YouTube oEmbed on 2026-10-23 (title + author match,
# embeddable). Provenance is mixed by necessity — some are official
# (AliceCooperVEVO, Beggars Banquet Records), the rest are the best-known
# archival recordings; the "meta" line states the facts either way.
MUSIC_PERFORMANCES = [
    {"id": "7DOzITFjq70", "title": "Michael Jackson — Thriller (Live)",
     "meta": "Munich · HIStory Tour, 1997 · 6:41",
     "channel": "LiveMJHD"},
    {"id": "d9QZgY4GG0M", "title": "Danny Elfman — This Is Halloween (Live)",
     "meta": "Hollywood Bowl · Halloween night, Oct 31, 2015 · 4:03",
     "channel": "Todd Malkin"},
    {"id": "2X-lWDPno-g",
     "title": "Ken Page — Oogie Boogie's Song (Live)",
     "meta": "Hollywood Bowl · Halloween night, Oct 31, 2015 · 2:38",
     "channel": "Todd Malkin"},
    {"id": "s7PGHF_kza8", "title": "Oingo Boingo — Dead Man's Party (Live)",
     "meta": "Farewell concert — their final show ever · Halloween night, "
             "Oct 31, 1995 · 8:14",
     "channel": "nutstothis"},
    {"id": "aOeP4p1fjMs",
     "title": "Alice Cooper — Welcome to My Nightmare (Live)",
     "meta": "Trashes the World Tour · 1990",
     "channel": "AliceCooperVEVO"},
    {"id": "d8RH8RO0eR0", "title": "Ghost — Year Zero (Live)",
     "meta": "Webster Hall, New York City · 2013 · 5:06",
     "channel": "Noisey"},
    {"id": "BwK4wItwgTc", "title": "Rob Zombie — Dragula (Live)",
     "meta": "Ozzfest · 2005 · TV broadcast · 4:32",
     "channel": "Tim Sipkes"},
    {"id": "MDvC7Q3KtZY", "title": "John Carpenter — Halloween Theme (Live)",
     "meta": "Aragon Ballroom, Chicago · Nov 9, 2017 · 4:11",
     "channel": "Sean Steffen"},
    {"id": "fDYbgLEUsMU", "title": "Bauhaus — Bela Lugosi's Dead (Live)",
     "meta": "Live · 7:39",
     "channel": "Beggars Banquet Records"},
    {"id": "vNuVifA7DSU",
     "title": "Bobby \"Boris\" Pickett — Monster Mash (Live on TV)",
     "meta": "Television performance · 1964 · 4:24",
     "channel": "NRRArchives2"},
]
# Full-length Halloween DJ sets & mixes (Dan, Oct 23). Same oEmbed
# discipline — verified 2026-10-23; every entry is a genuine full set
# (59+ minutes) on the DJ's or the series' own channel.
MUSIC_DJ_SETS = [
    {"id": "ZtOZu1LBBPE", "title": "RL Grime — Halloween XIII: The End",
     "meta": "The final chapter of his annual Halloween mix tradition · "
             "1:00:22",
     "channel": "RL Grime"},
    {"id": "e0QtfusVfas",
     "title": "RL Grime — Halloween X (Live at the Hollywood Palladium)",
     "meta": "Recorded live at the Hollywood Palladium · 1:15:24",
     "channel": "RL Grime"},
    {"id": "tufnSNynF4Q",
     "title": "deadmau5 — mau5trap radio 371: A Special Halloween Mix",
     "meta": "His own Halloween special on mau5trap radio · 1:00:00",
     "channel": "deadmau5"},
    {"id": "257wOj5Eh5o", "title": "Justin Jay — Boiler Room x Escape Halloween",
     "meta": "Live from Escape Halloween · 1:03:14",
     "channel": "Boiler Room"},
    {"id": "0yxIFBOzzRI", "title": "So — Boiler Room x Dommune Halloween",
     "meta": "Tokyo's Dommune Halloween session · 1:13:21",
     "channel": "Boiler Room"},
    {"id": "JGJoGtt3n5Y",
     "title": "Mikey Lion — Live from the Desert Hearts Halloween Party",
     "meta": "Desert Hearts' Halloween party, via Mixmag · 59:05",
     "channel": "Mixmag"},
    {"id": "VatiS3pNM00",
     "title": "Adam Beyer — Drumcode Halloween at Tobacco Dock",
     "meta": "Drumcode's London Halloween takeover · 2:02:17",
     "channel": "DJ Mag"},
    # WOGat2B7Vak (Timothy Caldwell's Spooky Vibes future bass mix) lived
    # here Oct 27 until Dan moved it up under the ZombieSquad feature —
    # see MUSIC_SPOTLIGHT_NEXT.
]
# Halloween singles not already on this page (Dan, Oct 23). oEmbed-verified
# 2026-10-23 on official/VEVO/label channels wherever they exist; where a
# song never got an official video, the meta line says "official audio"
# honestly, and the Time Warp is the studio-licensed Movieclips scene.
MUSIC_SINGLES = [
    {"id": "7YvAYIJSSZY", "title": "Rockwell — Somebody's Watching Me",
     "meta": "1984 · Michael Jackson sings the hook — Motown's paranoid "
             "classic",
     "channel": "RockwellVEVO"},
    {"id": "82cdnAUvsw8",
     "title": "Screamin' Jay Hawkins — I Put a Spell on You",
     "meta": "1956 · the original spell, screamed — official audio",
     "channel": "ScreaminJayVEVO"},
    {"id": "RZ2oXzrnti4", "title": "The Specials — Ghost Town",
     "meta": "1981 · the haunted ska anthem",
     "channel": "TheSpecialsOfficVEVO"},
    {"id": "HJWFsZ_YUc4", "title": "Ramones — Pet Sematary",
     "meta": "1989 · written for the Stephen King film",
     "channel": "Ramones"},
    {"id": "hIHUzBFlcW8", "title": "Siouxsie and the Banshees — Halloween",
     "meta": "1981 · from Ju Ju — official audio",
     "channel": "Siouxsie And The Banshees"},
    {"id": "D2MH5c2sTvc", "title": "Ministry — Every Day Is Halloween",
     "meta": "1984 · the goth-club anthem — official audio",
     "channel": "Ministry"},
    {"id": "auzfTPp4moA", "title": "Yeah Yeah Yeahs — Heads Will Roll",
     "meta": "2009 · off with their heads",
     "channel": "YeahYeahYeahsVEVO"},
    {"id": "qae25976UgA", "title": "Warren Zevon — Werewolves of London",
     "meta": "1978 · ah-hoo!",
     "channel": "RHINO"},
    {"id": "GU35oCHGhJ0", "title": "Donovan — Season of the Witch",
     "meta": "1966 · the psychedelic original — official audio",
     "channel": "DonovanVEVO"},
    {"id": "-w0WPkB3XJ4",
     "title": "The Rocky Horror Picture Show — Time Warp",
     "meta": "1975 · the film scene — it's just a jump to the left",
     "channel": "Movieclips"},
]
# Artist cards. "art" is the artist's own Spotify artist photo (Spotify CDN,
# via oEmbed) — Ghost's card uses their verified Dance Macabre video still
# instead, because Ghost's Spotify artist ID could not be verified from a
# citable source, so Ghost ships without a Spotify button rather than a
# guessed link.
_SP_ART = "https://open.spotify.com/artist/"
MUSIC_ICONS = [
    {"slug": "weeknd", "name": "The Weeknd",
     "art": "https://image-cdn-ak.spotifycdn.com/image/ab67616100005174c1719ac9e6a75c1c25835018",
     "claim": "Horror runs through his videos and sound — he even turned "
              "his After Hours era into a real haunted house at Universal's "
              "Halloween Horror Nights.",
     "spotify": _SP_ART + "1Xyo4u8uXC1ZmMpatF05PJ",
     "youtube": {"id": "dqRZDebPIGs", "label": "In Your Eyes (Official Video)"}},
    {"slug": "alice", "name": "Alice Cooper",
     "art": "https://image-cdn-fa.spotifycdn.com/image/ab6761610000517433b97c45348420d27fb92d68",
     "claim": "The original shock rocker — guillotines, snakes and a stage "
              "show built like a haunted house. Still touring this Halloween.",
     "spotify": _SP_ART + "3EhbVgyfGd7HkpsagwL9GS",
     "youtube": {"id": "Qq4j1LtCdww", "label": "Poison"},
     "pin": {"url": "/d/3654",
             "label": "🎃 See his HauntMap event — Alice's Attic Tour, "
                      "Tropicana Atlantic City · Sat Oct 31 · 8pm"}},
    {"slug": "zombie", "name": "Rob Zombie",
     "art": "https://image-cdn-fa.spotifycdn.com/image/ab67616100005174f0e838d90c5a7b7676ff4c43",
     "claim": "Metal's monster-movie maker — Dragula on the stereo, and "
              "behind the camera he directed House of 1000 Corpses and the "
              "Halloween remakes.",
     "spotify": _SP_ART + "3HVdAiMNjYrQIKlOGxoGh5",
     "youtube": {"id": "EqQuihD0hoI", "label": "Dragula"}},
    {"slug": "elfman", "name": "Danny Elfman",
     "art": "https://image-cdn-ak.spotifycdn.com/image/ab67616100005174f741706530dbd36d43078b98",
     "claim": "Fronted Oingo Boingo (\"Dead Man's Party\"), then wrote every "
              "song in The Nightmare Before Christmas — and sang Jack "
              "Skellington himself.",
     "spotify": _SP_ART + "5qBZETtyzfYnXOobDXbmcD",
     "youtube": {"id": "ZVuToMilP0A", "label": "This Is Halloween"}},
    {"slug": "petras", "name": "Kim Petras",
     "art": "https://image-cdn-ak.spotifycdn.com/image/ab6761610000517415a73d2fd90eb732c846ce06",
     "claim": "Released two Halloween mixtapes — Turn Off the Light, "
              "Vol. 1 & 2 — with Elvira, Mistress of the Dark, as a guest.",
     "spotify": _SP_ART + "3Xt3RrJMFv5SZkCfUE8C1J",
     "youtube": {"id": "DSbgQE5x2QM",
                 "label": "Turn Off the Light (feat. Elvira)"}},
    {"slug": "ghost", "name": "Ghost",
     "art": "https://i.ytimg.com/vi/7Gr63DiEUxw/hqdefault.jpg",
     "claim": "A masked metal mass led by Papa Emeritus — \"Dance Macabre\" "
              "and \"Mary on a Cross\" turned their ritual into Halloween "
              "anthems.",
     "spotify": None,
     "youtube": {"id": "7Gr63DiEUxw", "label": "Dance Macabre"}},
    {"slug": "jackson", "name": "Michael Jackson",
     "art": "https://image-cdn-ak.spotifycdn.com/image/ab67616100005174997cc9a4aec335d46c9481fd",
     "claim": "\"Thriller\" didn't just top the charts — its video made "
              "Halloween musical, and it still rises every October.",
     "spotify": _SP_ART + "3fMbdgg4jU18AjLCKBhRSm",
     "youtube": {"id": "sOnqjkJTMaA", "label": "Thriller"}},
    {"slug": "carpenter", "name": "John Carpenter",
     "art": "https://image-cdn-fa.spotifycdn.com/image/ab6761610000517464cf0c1a41bfcfec7fc3ff6e",
     "claim": "He directed Halloween (1978) and composed the theme himself "
              "— the most famous five notes in horror.",
     "spotify": _SP_ART + "0hxQtmgWiPtEsDPeIuKxXq",
     "youtube": {"id": "nZ2RQuUFznA", "label": "Halloween Theme"}},
]
MUSIC_POP = [
    {"slug": "gaga", "name": "Lady Gaga",
     "art": "https://image-cdn-ak.spotifycdn.com/image/ab67616100005174aadc18cac8d48124357c38e6",
     "claim": "\"Bloody Mary\" became the Wednesday dance phenomenon — "
              "dark pop has a queen, and Halloween is her season.",
     "spotify": _SP_ART + "1HY2Jd0NmPuamShAr6KMms",
     "youtube": {"id": "VFwmKL5OL-Q", "label": "Bloody Mary (Official Audio)"}},
    {"slug": "billie", "name": "Billie Eilish",
     "art": "https://image-cdn-fa.spotifycdn.com/image/ab676161000051744a21b4760d2ecb7b0dcdc8da",
     "claim": "\"bury a friend\" built a hit out of the monster under the "
              "bed — whispers, glitches and all.",
     "spotify": _SP_ART + "6qqNVTkY8uBg9cP3Jd7DAH",
     "youtube": {"id": "HUHC9tYz8ik", "label": "bury a friend"}},
    {"slug": "rihanna", "name": "Rihanna",
     "art": "https://image-cdn-fa.spotifycdn.com/image/ab67616100005174cb565a8e684e3be458d329ac",
     "claim": "\"Disturbia\" is the dark-pop staple that lands on Halloween "
              "playlists every single year.",
     "spotify": _SP_ART + "5pKCCKE2ajJHZ9KAiaK11H",
     "youtube": {"id": "E1mU6h4Xdxc", "label": "Disturbia"}},
]


@app.get("/music", response_class=HTMLResponse)
def music_page(request: Request):
    return templates.TemplateResponse(
        request, "music.html",
        {"site_name": SITE_NAME, "playlists": MUSIC_SPOTIFY_PLAYLISTS,
         "radio_stations": MUSIC_RADIO_IHEART,
         "edm_channels": MUSIC_EDM_CHANNELS,
         "hiphop_stations": MUSIC_HIPHOP_STATIONS,
         "yt_spotlight": MUSIC_SPOTLIGHT,
         "yt_spotlight_next": MUSIC_SPOTLIGHT_NEXT,
         "yt_featured": MUSIC_YOUTUBE_FEATURED, "yt_grid": MUSIC_YOUTUBE_GRID,
         "yt_performances": MUSIC_PERFORMANCES, "yt_dj_sets": MUSIC_DJ_SETS,
         "yt_singles": MUSIC_SINGLES,
         "icons": MUSIC_ICONS, "pop": MUSIC_POP},
    )


# ---------------------------------------------------------------- movies
# /movies (Dan, Oct 23): the screening room — new Halloween-season releases,
# the classics and superfan deep cuts, every card a click-to-play YouTube
# facade for the official trailer (or, for Halloweentown, Disney Channel's
# own clip — Disney has never posted a trailer). Card art is the trailer's
# own YouTube still; no posters are downloaded or hotlinked. Every ID below
# was verified via YouTube oEmbed on 2026-10-23 (title + channel match,
# embeddable) — never add a link here without the same check. Release dates
# and the three R ratings are from the studios' own trailers and the
# October 2026 release calendars (see the staged build report).
MOVIE_NEW = [
    # Practical Magic pair (Dan, Oct 24): the full film is a Warner Bros.
    # title with NO legal free embed (HBO Max / transactional VOD only —
    # checked Oct 24), so the page carries the official trailers instead.
    # Both IDs oEmbed-verified 2026-10-24 (title + channel match,
    # embeddable).
    {"title": "Practical Magic 2", "year": 2026,
     "meta": "In theaters now · Sep 11",
     "blurb": "The Owens sisters return after 28 years — Bullock and "
              "Kidman face down the family curse as it reaches for the "
              "next generation. Based on Alice Hoffman's The Book of "
              "Magic.",
     "id": "Ho10_4IX1jE", "channel": "Warner Bros.",
     "kind": "Official Trailer"},
    {"title": "Resident Evil", "year": 2026,
     "meta": "In theaters now · Sep 18",
     "blurb": "Zach Cregger (Barbarian, Weapons) takes the keys to Raccoon "
              "City — the fall's biggest horror swing.",
     "id": "mNd1gb19A-c", "channel": "Sony Pictures Entertainment",
     "kind": "Official Trailer"},
    {"title": "Other Mommy", "year": 2026,
     "meta": "In theaters Oct 9 · Rated R",
     "blurb": "Jessica Chastain plays a mother — and the thing wearing her "
              "face. The season's creepiest double act.",
     "id": "bEpTgowZ1dI", "channel": "Universal Pictures",
     "kind": "Official Trailer"},
    {"title": "V/H/S/Mixtape", "year": 2026,
     "meta": "Streaming on Shudder · Oct 9",
     "blurb": "Found footage gets a soundtrack — this year's V/H/S "
              "anthology wires every scare to the music.",
     "id": "GrIouRKyPDw", "channel": "Shudder",
     "kind": "Official Trailer"},
    {"title": "Crawlers", "year": 2026,
     "meta": "In theaters Oct 16 · Rated R",
     "blurb": "Venomous spiders seal an apartment block — and a city "
              "quarantines it with everyone still inside. Eight legs, no "
              "exits.",
     "id": "4DowjB87tRE", "channel": "RoadsideFlix",
     "kind": "Official Trailer"},
    {"title": "Whalefall", "year": 2026,
     "meta": "In theaters Oct 16",
     "blurb": "Swallowed whole by a sperm whale with an hour of air left "
              "— the survival nightmare you'll feel in your chest.",
     "id": "rN9F6-tbySY", "channel": "20th Century Studios",
     "kind": "Official Trailer"},
    {"title": "Clayface", "year": 2026,
     "meta": "In theaters Oct 23 · Rated R",
     "blurb": "DC goes full body horror — a disfigured actor, a desperate "
              "experiment, and Gotham's most tragic monster, landing the "
              "weekend before Halloween.",
     "id": "OGO4Mqvo3jI", "channel": "DC",
     "kind": "Official Trailer"},
    # Scream 7 + Scary Movie pair (Dan, Oct 24): both franchises are
    # Miramax/Paramount copyright — NO legal free full-length embed
    # exists (subscription streaming / transactional VOD only, checked
    # Oct 24), so the page carries the official trailers instead. All
    # IDs below oEmbed-verified 2026-10-24 (title + channel match,
    # embeddable). The 1996 Scream trailer was already in The Classics
    # (Paramount Movies) — not duplicated.
    {"title": "Scream 7", "year": 2026,
     "meta": "In theaters Feb 27",
     "blurb": "Sidney Prescott is back. A new Ghostface finds the quiet "
              "town where she built her life — and her daughter is the "
              "target. Kevin Williamson, who wrote the 1996 original, "
              "directs.",
     "id": "UJrghaPJ0RY", "channel": "Paramount Pictures",
     "kind": "Official Trailer"},
    {"title": "Scary Movie 6", "year": 2026,
     "meta": "In theaters Jun 5",
     "blurb": "The Core Four rides again — Cindy, Brenda, Shorty and Ray "
              "reunite 26 years later to slash through every reboot, "
              "requel and elevated-horror hit of the last decade. No "
              "trope survives.",
     "id": "0fZ58S-7QP0", "channel": "Paramount Pictures",
     "kind": "Official Trailer"},
]
MOVIE_CLASSICS = [
    {"title": "The Rocky Horror Picture Show", "year": 1975,
     "blurb": "Fifty years of midnight crowds still do the Time Warp in "
              "costume. Not a screening — a ritual.",
     "id": "4plqh6obZW4", "channel": "20th Century Studios",
     "kind": "Official Trailer"},
    {"title": "Halloween", "year": 1978,
     "blurb": "The night he came home. Carpenter's shoestring slasher "
              "wrote the blueprint horror still follows — and Haddonfield "
              "is sacred ground.",
     "id": "3JsrH8eUVOo", "channel": "Scream Factory TV",
     "kind": "Official Trailer"},
    {"title": "Beetlejuice", "year": 1988,
     "blurb": "The ghost with the most turned a haunted house into a "
              "comedy club. Go ahead — say his name three times.",
     "id": "po1HJbmow0g", "channel": "Warner Bros. Entertainment",
     "kind": "Official Trailer"},
    {"title": "Hocus Pocus", "year": 1993,
     "blurb": "Three resurrected witches, one black-flame candle, "
              "infinite rewatches. The official film of October.",
     "id": "F4e6YQFrt1s", "channel": "Rotten Tomatoes Classic Trailers",
     "kind": "Official Trailer"},
    {"title": "The Nightmare Before Christmas", "year": 1993,
     "blurb": "Halloween movie or Christmas movie? Superfans settled it "
              "long ago: it's both, forever — and Halloween Town is home.",
     "id": "wr6N_hZyBCk", "channel": "Rotten Tomatoes Classic Trailers",
     "kind": "Official Trailer"},
    {"title": "Scream", "year": 1996,
     "blurb": "The film that made horror self-aware — and made every "
              "ringing phone in 1996 sound like a threat.",
     "id": "U0LETmDvuXc", "channel": "Paramount Movies",
     "kind": "Official Trailer"},
    {"title": "Practical Magic", "year": 1998,
     "blurb": "Two witch sisters, one family curse: every man who loves "
              "an Owens woman is doomed. Bullock and Kidman's midnight-"
              "margarita classic — the coziest spell of the season. Its "
              "official trailer, from Warner Bros.' own vault channel.",
     "id": "R7uixLkpjPs", "channel": "Warner Bros. Rewind",
     "kind": "Official Trailer"},
    {"title": "Halloweentown", "year": 1998,
     "blurb": "Disney Channel's 1998 original is pure bottled nostalgia — "
              "Grandma Aggie, a giant pumpkin in the town square, and a "
              "town where it's always Halloween.",
     "id": "ozGLDYRjvN0", "channel": "Disney Channel",
     "kind": "Official Clip"},
    {"title": "Scary Movie", "year": 2000,
     "blurb": "The parody that took a chainsaw to the rules — the "
              "Wayans brothers and Anna Faris spoof Scream, The Sixth "
              "Sense and every teen-slasher cliché in the book. Wazzup!",
     "id": "HTLPULt0eJ4", "channel": "Miramax",
     "kind": "Official Trailer"},
    {"title": "Trick 'r Treat", "year": 2007,
     "blurb": "Sam's rules are the superfans' rules: wear a costume, hand "
              "out treats, and never blow out a jack-o'-lantern early.",
     "id": "ZTOHbEOLcCU", "channel": "Legendary",
     "kind": "Official Trailer"},
    {"title": "Coraline", "year": 2009,
     "blurb": "The 'kids' movie that genuinely terrifies adults. Button "
              "eyes beat jump scares, every single time.",
     "id": "P8lfdvXkhu0", "channel": "LAIKA Studios",
     "kind": "Official Trailer"},
]
MOVIE_DEEP_CUTS = [
    {"title": "The Monster Squad", "year": 1987,
     "blurb": "Kids vs. Dracula, Frankenstein's monster and the Wolfman "
              "— the '80s clubhouse horror that raised a generation of "
              "superfans.",
     "id": "bdLO3riTwJU", "channel": "Arrow Video",
     "kind": "Official Trailer"},
    {"title": "Ginger Snaps", "year": 2000,
     "blurb": "Puberty as lycanthropy — Canada's sharpest cult classic, "
              "and the werewolf movie superfans gatekeep hardest.",
     "id": "011YdVip2KM", "channel": "Lionsgate Movies",
     "kind": "Official Trailer"},
    {"title": "Shaun of the Dead", "year": 2004,
     "blurb": "A rom-com with zombies that loves the genre too much to "
              "mock it. The Cornetto standard, set in a London pub.",
     "id": "cqDy3dXLBO8", "channel": "Focus Features",
     "kind": "Official Trailer"},
    {"title": "Monster House", "year": 2006,
     "blurb": "The house across the street is literally alive — animated "
              "suburbia with real teeth, and a finale that goes full "
              "monster movie.",
     "id": "2bhP8oH1TJs", "channel": "Amblin Entertainment",
     "kind": "Official Trailer"},
    {"title": "The House of the Devil", "year": 2009,
     "blurb": "Shot like a lost tape from 1983 — Ti West's babysitter "
              "slow-burn is the purist's pick, Walkman and all.",
     "id": "z9vJF61_NLU", "channel": "Magnolia Pictures & Magnet Releasing",
     "kind": "Official Trailer"},
    {"title": "ParaNorman", "year": 2012,
     "blurb": "A boy who talks to the dead saves a town that fears him — "
              "LAIKA's stop-motion love letter to every weird kid who "
              "loves horror.",
     "id": "skGT6aorNng", "channel": "LAIKA Studios",
     "kind": "Official Trailer"},
    {"title": "What We Do in the Shadows", "year": 2014,
     "blurb": "Four vampire flatmates, one documentary crew — the "
              "funniest bloodsuckers ever filmed, straight out of "
              "Wellington.",
     "id": "IAZEWtyhpes", "channel": "Madman Films",
     "kind": "Official Trailer"},
]
# Free Full Movies (Dan, Oct 24): the whole film, free and legal — embeds
# only, never re-hosted. The nine classics are public domain in the US and
# stream from the Internet Archive's own player (embed:
# https://archive.org/embed/<id>; card art is IA's item-image service).
# The one modern title streams from Kings of Horror, a rights-holder
# channel (Blue Sky Media LLC), verified via YouTube oEmbed on 2026-10-24
# (title + channel match, embeddable). Full rights research per title:
# free-full-movies-catalog.md in the goal's movies-catalog folder — check
# it before adding, swapping or "upgrading" any print here (some famous
# titles, e.g. Horror Express, are NOT as public domain as claimed).
MOVIE_FREE_FULL = [
    {"title": "Night of the Living Dead", "year": 1968,
     "blurb": "Romero's original nightmare — the dead walk in rural "
              "Pennsylvania and modern horror is born.",
     "host": "ia", "id": "night-of-the-living-dead-1968",
     "channel": "Internet Archive", "kind": "Full Movie", "pd": True},
    {"title": "House on Haunted Hill", "year": 1959,
     "blurb": "Vincent Price offers five guests $10,000 to survive one "
              "night in a haunted house. William Castle's beloved bag of "
              "tricks.",
     "host": "ia", "id": "house-on-haunted-hill",
     "channel": "Internet Archive", "kind": "Full Movie", "pd": True},
    {"title": "Carnival of Souls", "year": 1962,
     "blurb": "After a car crash, an organist is drawn to an abandoned "
              "carnival — and a pale stranger keeps appearing. Dream-logic "
              "dread on a shoestring.",
     "host": "ia", "id": "CarnivalofSouls",
     "channel": "Internet Archive", "kind": "Full Movie", "pd": True},
    {"title": "The Last Man on Earth", "year": 1964,
     "blurb": "Vincent Price, last survivor of a plague — the first "
              "I Am Legend adaptation, decades before Will Smith.",
     "host": "ia", "id": "lastmanonearth-1964",
     "channel": "Internet Archive", "kind": "Full Movie", "pd": True},
    {"title": "The Little Shop of Horrors", "year": 1960,
     "blurb": "A meek florist, a man-eating plant, and a blink-and-miss "
              "cameo by a young Jack Nicholson. Feed me, Seymour.",
     "host": "ia", "id": "the-little-shop-of-horrors",
     "channel": "Internet Archive", "kind": "Full Movie", "pd": True},
    {"title": "Dementia 13", "year": 1963,
     "blurb": "A scheming widow, a drowned sister, an axe murderer — "
              "Francis Ford Coppola's directorial debut, made for Roger "
              "Corman.",
     "host": "ia", "id": "dementia-13-1963_202312",
     "channel": "Internet Archive", "kind": "Full Movie", "pd": True},
    {"title": "White Zombie", "year": 1932,
     "blurb": "Bela Lugosi staffs a Haitian sugar mill with zombie "
              "labor — the first feature-length zombie film ever made.",
     "host": "ia", "id": "white_zombie",
     "channel": "Internet Archive", "kind": "Full Movie", "pd": True},
    {"title": "Nosferatu", "year": 1922,
     "blurb": "Murnau's unauthorized Dracula. Max Schreck's Count Orlok "
              "still casts the longest shadow in horror — complete "
              "93-minute tinted print.",
     "host": "ia", "id": "Nosferatu_most_complete_version_93_mins.",
     "channel": "Internet Archive", "kind": "Full Movie", "pd": True},
    {"title": "The Cabinet of Dr. Caligari", "year": 1920,
     "blurb": "The twisted sets that started it all — German "
              "expressionism's founding nightmare, silent with its "
              "original German intertitles.",
     "note": "Silent · German intertitles",
     "host": "ia", "id": "1919DasCabinetDesDr.Caligari",
     "channel": "Internet Archive", "kind": "Full Movie", "pd": True},
    {"title": "The Night Devours", "year": 2024,
     "blurb": "A modern indie chiller from a verified distributor "
              "channel — a killer's confessions unravel into something "
              "far worse. Full feature, officially licensed.",
     "host": "yt", "id": "qGGTwchOUys",
     "channel": "Kings of Horror", "kind": "Full Movie", "pd": False},
]


@app.get("/movies", response_class=HTMLResponse)
def movies_page(request: Request):
    return templates.TemplateResponse(
        request, "movies.html",
        {"site_name": SITE_NAME, "new": MOVIE_NEW,
         "classics": MOVIE_CLASSICS, "deep_cuts": MOVIE_DEEP_CUTS,
         "free_full": MOVIE_FREE_FULL},
    )


# ------------------------------------------------------- pop haunt culture
# /pop-haunt-culture (Dan, Oct 27): Halloween in pop culture — the iconic
# movie/TV moments, music videos, costumes and viral clips the season
# lives on. Same construction as /movies and /music: hand-picked entries
# in plain lists below (adding one is a data change, not a redesign),
# every card a click-to-play YouTube facade, card art the video's own
# YouTube still. Every ID must be verified via YouTube oEmbed before it
# is added (real title + channel match, embeddable). Verified on
# 2026-10-27: the lead below and the grid's first two entries, all
# oEmbed-verified — "NYC Halloween 2026 Decorations in Brooklyn"
# and "Thriller Dance NYC Halloween Parade 2026 (Behind the
# Scenes)", both by The NYC Walking Show, and "The Halloween
# Episode" by Friends Keep Secrets. Display titles drop the
# hashtags/emoji the raw oEmbed titles carry; the words are the
# creators' own.
POP_CULTURE_FEATURED = {
    "id": "aG-2lzbCf30",
    "title": "NYC Halloween 2026 Decorations in Brooklyn New York "
             "BEST Halloween Outdoor Yard Decorations 4K",
    "channel": "The NYC Walking Show",
    "kind": "Video",
    "blurb": "Dan's top feature: a 4K walk through Brooklyn's most "
             "decorated Halloween houses — porches stacked with "
             "skeletons, clowns and color.",
}
# The collection grid. Dan feeds entries one at a time; append dicts of
# {"id", "title", "channel", "kind", "blurb"} — the template renders
# them as cards next to the featured pick. The Shorts below were all
# verified via oEmbed on 2026-10-27 (embeddable); "short": True marks
# a vertical YouTube Short so the card frames its still uncropped.
# Non-YouTube entries carry "platform" + "url" + "thumb" (a local
# cover-frame file in static/img/): the template renders the local
# still and the click handler swaps in that platform's official embed.
POP_CULTURE_GRID: list[dict] = [
    # First Facebook entry (Dan, 2026-10-27): Dude Dad's couples-costume
    # reel, shared by Dan as a facebook.com/share/r link and resolved
    # via the Facebook connector. Public reel (posted Oct 26, 2026);
    # the still is the reel's own cover frame from Facebook's plugin
    # page (the video itself is never re-hosted — tap swaps in
    # Facebook's official embedded player).
    {"id": "2305908356865207",
     "platform": "facebook",
     "url": "https://www.facebook.com/reel/2305908356865207/",
     "thumb": "/static/img/dude_dad_couples_costumes.jpg",
     "title": "What's Your Best Couples Costume Idea?",
     "channel": "Dude Dad",
     "kind": "Facebook Reel", "short": True,
     "blurb": "Five couples costumes in one reel — Dolly Parton "
              "beside a Little Free Library, a bride and groom, a "
              "swashbuckler, Nemo, even an AI data center that takes "
              "two people to wear — then he asks for yours."},
    {"id": "kxXVk4UI0WI",
     "title": "Thriller Dance NYC Halloween Parade 2026 "
              "(Behind the Scenes): Michael Jackson Zombie Dance "
              "Rehearsal",
     "channel": "The NYC Walking Show",
     "kind": "Video",
     "blurb": "Behind the scenes at the Thriller rehearsal for New "
              "York's Halloween Parade — dozens of dancers in zombie "
              "gear running Michael Jackson's most famous "
              "choreography."},
    {"id": "jWCpbCsOKis",
     "title": "The Halloween Episode",
     "channel": "Friends Keep Secrets",
     "kind": "Video",
     "blurb": "The Halloween episode from Friends Keep Secrets — "
              "the video that opened Pop Haunt Culture."},
    {"id": "gssmks0iCAQ",
     "title": "Crazy Halloween Makeup Illusion",
     "channel": "Leah Comptonn",
     "kind": "YouTube Short", "short": True,
     "blurb": "A clown makeup illusion in under a minute — the face "
              "melts into a grin that isn't hers."},
    {"id": "0xl5AKjy99c",
     "title": "Ranking the Most Unexpected Halloween Makeup, Pt. 1",
     "channel": "Ranked Looks",
     "kind": "YouTube Short", "short": True,
     "blurb": "Ranked Looks counts down the Halloween makeup looks "
              "nobody saw coming."},
    {"id": "yT_3qDBL8FE",
     "title": "I Ranked New Halloween Costume Trend of 2026 (Part 8)",
     "channel": "Thalynea",
     "kind": "YouTube Short", "short": True,
     "blurb": "Thalynea ranks the new Halloween costume trends of "
              "2026 — part 8 of the series."},
    {"id": "_51_XhE32C4",
     "title": "Ranking the Best Halloween Makeup Trend",
     "channel": "Mind Forge",
     "kind": "YouTube Short", "short": True,
     "blurb": "Mind Forge ranks the best Halloween makeup trends, "
              "from a scary smile to the Venom couple."},
    {"id": "2gYHYNUTqlk",
     "title": "Best Halloween Costume Trend of 2026! Got Ranked (Part 9)",
     "channel": "Thalynea",
     "kind": "YouTube Short", "short": True,
     "blurb": "Thalynea's costume-trend rankings roll on — part 9 "
              "of the series."},
    {"id": "hSsUwFuDhPY",
     "title": "2010 vs 2026 Halloween Makeup — Save This for Inspo",
     "channel": "Ella Nysss",
     "kind": "YouTube Short", "short": True,
     "blurb": "Ella Nysss puts 2010 Halloween makeup side by side "
              "with 2026's take on the same look."},
    {"id": "Hkg98AnpeaI",
     "title": "Top 5 Halloween Costumes You'll See Everywhere in 2026",
     "channel": "Trey Eversman",
     "kind": "YouTube Short", "short": True,
     "blurb": "Trey Eversman calls the five costumes you'll see "
              "everywhere this Halloween."},
]


@app.get("/pop-haunt-culture", response_class=HTMLResponse)
def pop_culture_page(request: Request):
    return templates.TemplateResponse(
        request, "pop_culture.html",
        {"site_name": SITE_NAME, "featured": POP_CULTURE_FEATURED,
         "grid": POP_CULTURE_GRID},
    )


# Sponsor-facing counts are HUMAN page views only: machine paths are
# excluded (Oct 26, 2026 correction — /healthz health-check pings were
# being logged in page_views and counted as views, and every ping
# carried its own sid so each one also counted as a separate "visit":
# 68,573 pings through Oct 26). /admin/stats keeps the raw request
# count for ops; the media kit never quotes it.
_MK_HUMAN = "path NOT IN ('/healthz', '/sitemap.xml') AND path NOT LIKE '/api/%'"


def _mk_visitors(today_d) -> dict:
    """Media-kit visitor counts: distinct session ids on human page
    views, today / last 7 days. TTL-cached per UTC date (fortification
    pass 2): each count was a COUNT(DISTINCT sid) scan over the whole
    page_views table (the substr() date filter defeats the date index)
    on every /media-kit render."""
    def build():
        week_start_d = today_d - timedelta(days=6)
        with get_conn(DB_PATH) as conn:
            today = conn.execute(
                "SELECT COUNT(DISTINCT sid) FROM page_views WHERE substr(viewed_at, 1, 10) = ? AND " + _MK_HUMAN,
                (today_d.isoformat(),)).fetchone()[0]
            week = conn.execute(
                "SELECT COUNT(DISTINCT sid) FROM page_views WHERE substr(viewed_at, 1, 10) >= ? AND " + _MK_HUMAN,
                (week_start_d.isoformat(),)).fetchone()[0]
        return {"today": today, "week": week}
    return dict(_ttl_cached(f"mkvis:{today_d.isoformat()}", build))


def _mk_total_views() -> int:
    """Media-kit all-time total HUMAN page views (machine paths
    excluded via _MK_HUMAN — see the Oct 26 note above). TTL-cached
    like the other kit aggregates (fortification pass 2 pattern)."""
    def build():
        with get_conn(DB_PATH) as conn:
            return conn.execute(
                "SELECT COUNT(*) FROM page_views WHERE " + _MK_HUMAN).fetchone()[0]
    return int(_ttl_cached("mktotalviews", build))


def _mk_geo() -> dict:
    """Media-kit geographic spread: distinct town labels + states
    across ALL categories. TTL-cached (fortification pass 2) — it was
    a DISTINCT scan of every entry's town per render."""
    def build():
        with get_conn(DB_PATH) as conn:
            town_rows = conn.execute(
                "SELECT DISTINCT town FROM entries WHERE hidden = 0").fetchall()
        labels: set[str] = set()
        state_set: set[str] = set()
        for r in town_rows:
            label = extract_city_state(r["town"] or "")
            if label:
                labels.add(label)
            st = extract_state(r["town"] or "")
            if st:
                state_set.add(st)
        return {"town_count": len(labels), "states": sorted(state_set),
                "state_count": len(state_set - {"DC"}),
                "has_dc": "DC" in state_set}
    b = _ttl_cached("mkgeo", build)
    return {**b, "states": list(b["states"])}


@app.get("/media-kit", response_class=HTMLResponse)
def media_kit(request: Request):
    now = datetime.now(timezone.utc)
    today_d = now.date()
    week_start_d = today_d - timedelta(days=6)
    fmt_day = "%B %-d, %Y"
    kit = {
        "updated": today_d.strftime(fmt_day),
        "today_label": today_d.strftime(fmt_day),
        "week_range": f"{week_start_d.strftime(fmt_day)} – {today_d.strftime(fmt_day)}",
        "visitors_today": 0,
        "visitors_week": 0,
        "total_views": 0,
        "total_pins": 0,
        "categories": [],
        "town_count": 0,
        "states": [],
        "games": MEDIA_KIT_GAMES,
    }
    # Fortification pass 2: every aggregate below is TTL-cached (see
    # _mk_visitors / _mk_geo / _category_counts) — this sponsor-facing
    # page re-scanned page_views twice and entries twice per render
    # for numbers where ≤2-minute staleness is invisible.
    try:
        vis = _mk_visitors(today_d)
        kit["visitors_today"] = vis["today"]
        kit["visitors_week"] = vis["week"]
    except Exception:
        pass
    try:
        kit["total_views"] = _mk_total_views()
    except Exception:
        pass
    counts = _category_counts()
    kit["total_pins"] = sum(counts.values())
    kit["categories"] = [
        {"label": label, "count": counts[key]}
        for key, label in MEDIA_KIT_CATEGORY_LABELS if counts.get(key)
    ]
    geo = _mk_geo()
    kit["town_count"] = geo["town_count"]
    kit["states"] = geo["states"]
    kit["state_count"] = geo["state_count"]
    kit["has_dc"] = geo["has_dc"]
    return templates.TemplateResponse(
        request, "media_kit.html", {"kit": kit, "site_name": SITE_NAME},
    )


# ---------------------------------------------------------------- costume contest

COSTUME_SQL = """CREATE TABLE IF NOT EXISTS costume_entries (
    id INTEGER PRIMARY KEY,
    display_name TEXT,
    title TEXT NOT NULL,
    media_path TEXT NOT NULL,
    thumb_path TEXT,
    votes INTEGER DEFAULT 0,
    hidden INTEGER DEFAULT 0,
    created_at TEXT
)"""


@app.get("/costume-contest", response_class=HTMLResponse)
def costume_contest(request: Request):
    voted = set()
    for part in request.cookies.get("costume_votes", "").split(","):
        if part.strip().isdigit():
            voted.add(int(part.strip()))
    with get_conn(DB_PATH) as conn:
        conn.execute(COSTUME_SQL)
        rows = conn.execute(
            "SELECT * FROM costume_entries WHERE hidden = 0 ORDER BY votes DESC, id DESC"
        ).fetchall()
    costumes = []
    for r in rows:
        c = dict(r)
        c["media_url"] = f"/media/{c['media_path']}"
        c["thumb_url"] = f"/media/{c['thumb_path']}" if c.get("thumb_path") else c["media_url"]
        c["voted"] = c["id"] in voted
        costumes.append(c)
    leader = costumes[0] if costumes and costumes[0]["votes"] > 0 else None
    return templates.TemplateResponse(
        request, "costume_contest.html",
        {"costumes": costumes, "leader": leader, "site_name": SITE_NAME,
         "error": request.query_params.get("error")},
    )


@app.post("/costume-contest/upload")
async def costume_upload(
    title: str = Form(...),
    display_name: str = Form(""),
    media: UploadFile = File(...),
):
    ext = safe_ext(media.filename or "")
    if ext not in PHOTO_EXTS:
        return RedirectResponse("/costume-contest?error=Please+choose+a+photo+(JPG,+PNG+or+WebP).", status_code=303)

    # Image decode + thumbnail and the insert run in the thread pool,
    # never on the event loop (blip hardening, Oct 25) — original flow.
    def _store() -> RedirectResponse:
        try:
            tmp = save_upload(media, MAX_PHOTO_BYTES)
            try:
                with Image.open(tmp) as im:
                    im.verify()
            except (UnidentifiedImageError, OSError):
                tmp.unlink(missing_ok=True)
                return RedirectResponse("/costume-contest?error=That+file+isn%27t+a+readable+image.", status_code=303)
            name = uuid.uuid4().hex
            media_rel = f"{name}{ext}"
            shutil.move(tmp, UPLOAD_DIR / media_rel)
            try:
                thumb_rel = make_thumb(UPLOAD_DIR / media_rel, name)
            except (OSError, UnidentifiedImageError):
                (UPLOAD_DIR / media_rel).unlink(missing_ok=True)
                return RedirectResponse("/costume-contest?error=Couldn%27t+process+that+image.", status_code=303)
        except ValueError:
            return RedirectResponse("/costume-contest?error=That+photo+is+too+large+(10+MB+max).", status_code=303)
        with get_conn(DB_PATH) as conn:
            conn.execute(COSTUME_SQL)
            conn.execute(
                "INSERT INTO costume_entries (display_name, title, media_path, thumb_path, votes, hidden, created_at) VALUES (?, ?, ?, ?, 0, 0, ?)",
                ((display_name or "").strip()[:60] or None, title.strip()[:120], media_rel, thumb_rel,
                 datetime.now(timezone.utc).isoformat()),
            )
        return RedirectResponse("/costume-contest", status_code=303)

    return await run_in_threadpool(_store)


@app.post("/costume-contest/{cid}/vote")
def costume_vote(cid: int, request: Request):
    voted = set()
    for part in request.cookies.get("costume_votes", "").split(","):
        if part.strip().isdigit():
            voted.add(int(part.strip()))
    with get_conn(DB_PATH) as conn:
        conn.execute(COSTUME_SQL)
        row = conn.execute("SELECT votes FROM costume_entries WHERE id = ? AND hidden = 0", (cid,)).fetchone()
        if row is None:
            return JSONResponse({"error": "not found"}, status_code=404)
        votes = row["votes"]
        if cid in voted:
            votes = max(0, votes - 1)
            voted.discard(cid)
            now_voted = False
        else:
            votes += 1
            voted.add(cid)
            now_voted = True
        conn.execute("UPDATE costume_entries SET votes = ? WHERE id = ?", (votes, cid))
    resp = JSONResponse({"votes": votes, "voted": now_voted})
    resp.set_cookie("costume_votes", ",".join(str(v) for v in sorted(voted)),
                    max_age=60 * 60 * 24 * 120, path="/", samesite="lax")
    return resp



# Art in Motion (Dan, Oct 27, 2026): @olesamhain's complete TikTok
# catalogue — handmade Halloween props and displays, embed-only via
# click-to-play facades on /fan-art (covers are each video's own
# frame, downloaded to static/img). All 39 profile videos retrieved
# and oEmbed-verified on 2026-10-27; every one is the creator's own
# prop/display art, so none were skipped. Newest first.
ART_VIDEOS: list[dict] = [
    {"video_id": '7701397572111404301',
     "url": 'https://www.tiktok.com/@olesamhain/video/7701397572111404301',
     "title": "It's Halloween week, with just a few days left!",
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7701397572111404301.jpg',
     "posted": 'Oct 27, 2026'},
    {"video_id": '7651697024068373773',
     "url": 'https://www.tiktok.com/@olesamhain/video/7651697024068373773',
     "title": 'Photodump from the 2024 display, inspired by a 1920’s American Halloween party, the Dennison Bogie Book, specifically!',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7651697024068373773.jpg',
     "posted": 'Jun 15, 2026'},
    {"video_id": '7651694977461816589',
     "url": 'https://www.tiktok.com/@olesamhain/video/7651694977461816589',
     "title": 'Bogey Ball: Hallowe’en 1923 (2024)',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7651694977461816589.jpg',
     "posted": 'Jun 15, 2026'},
    {"video_id": '7649929788454440206',
     "url": 'https://www.tiktok.com/@olesamhain/video/7649929788454440206',
     "title": 'the last paint job before the 2024 display, the sky was so beautiful 🎃🌙',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7649929788454440206.jpg',
     "posted": 'Jun 11, 2026'},
    {"video_id": '7645264420179856653',
     "url": 'https://www.tiktok.com/@olesamhain/video/7645264420179856653',
     "title": 'Strange totems have been appearing at the edge of these woods for decades…',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7645264420179856653.jpg',
     "posted": 'May 29, 2026'},
    {"video_id": '7638595684119088397',
     "url": 'https://www.tiktok.com/@olesamhain/video/7638595684119088397',
     "title": 'In the garage…',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7638595684119088397.jpg',
     "posted": 'May 11, 2026'},
    {"video_id": '7634341785258446094',
     "url": 'https://www.tiktok.com/@olesamhain/video/7634341785258446094',
     "title": '2026 witch is pretty much finished. Fixing up her mouth and adding some glossy, wet grime in a few spots',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7634341785258446094.jpg',
     "posted": 'Apr 30, 2026'},
    {"video_id": '7632320983222865166',
     "url": 'https://www.tiktok.com/@olesamhain/video/7632320983222865166',
     "title": 'New witch in progress for 2026',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7632320983222865166.jpg',
     "posted": 'Apr 24, 2026'},
    {"video_id": '7625067786108259597',
     "url": 'https://www.tiktok.com/@olesamhain/video/7625067786108259597',
     "title": 'Halloween Props — Home Haunt',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7625067786108259597.jpg',
     "posted": 'Apr 5, 2026'},
    {"video_id": '7622528133010296077',
     "url": 'https://www.tiktok.com/@olesamhain/video/7622528133010296077',
     "title": 'Halloween 2023: AMERICAN WITCHCRAFT',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7622528133010296077.jpg',
     "posted": 'Mar 29, 2026'},
    {"video_id": '7620654425312447758',
     "url": 'https://www.tiktok.com/@olesamhain/video/7620654425312447758',
     "title": 'The October Country - 2026',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7620654425312447758.jpg',
     "posted": 'Mar 24, 2026'},
    {"video_id": '7619498170594184461',
     "url": 'https://www.tiktok.com/@olesamhain/video/7619498170594184461',
     "title": 'grim evidence | 3/20',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7619498170594184461.jpg',
     "posted": 'Mar 21, 2026'},
    {"video_id": '7619373051934756110',
     "url": 'https://www.tiktok.com/@olesamhain/video/7619373051934756110',
     "title": 'His feet sank into the moss-covered slime.',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7619373051934756110.jpg',
     "posted": 'Mar 20, 2026'},
    {"video_id": '7613781921478315278',
     "url": 'https://www.tiktok.com/@olesamhain/video/7613781921478315278',
     "title": 'Corpse Prop — Home Haunt',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7613781921478315278.jpg',
     "posted": 'Mar 5, 2026'},
    {"video_id": '7612722035910790414',
     "url": 'https://www.tiktok.com/@olesamhain/video/7612722035910790414',
     "title": 'Some detail painting and playing around with my flood lights yesterday :)',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7612722035910790414.jpg',
     "posted": 'Mar 2, 2026'},
    {"video_id": '7611761195292347661',
     "url": 'https://www.tiktok.com/@olesamhain/video/7611761195292347661',
     "title": 'Halloween 2026: The October Country',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7611761195292347661.jpg',
     "posted": 'Feb 28, 2026'},
    {"video_id": '7610528320760990989',
     "url": 'https://www.tiktok.com/@olesamhain/video/7610528320760990989',
     "title": 'Body Snatcher | 2.24 In the garage, starting to paint this scarecrow',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7610528320760990989.jpg',
     "posted": 'Feb 24, 2026'},
    {"video_id": '7609963019266805006',
     "url": 'https://www.tiktok.com/@olesamhain/video/7609963019266805006',
     "title": 'here comes the snow ❤️',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7609963019266805006.jpg',
     "posted": 'Feb 23, 2026'},
    {"video_id": '7609824167298387214',
     "url": 'https://www.tiktok.com/@olesamhain/video/7609824167298387214',
     "title": 'some of my antiques, Halloween in the 20’s/30’s was amazing',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7609824167298387214.jpg',
     "posted": 'Feb 22, 2026'},
    {"video_id": '7607675008441208077',
     "url": 'https://www.tiktok.com/@olesamhain/video/7607675008441208077',
     "title": 'Playing around with lights in the basement, finishing up some painting ❤️',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7607675008441208077.jpg',
     "posted": 'Feb 17, 2026'},
    {"video_id": '7607498672640691470',
     "url": 'https://www.tiktok.com/@olesamhain/video/7607498672640691470',
     "title": 'Trick or treat?',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7607498672640691470.jpg',
     "posted": 'Feb 16, 2026'},
    {"video_id": '7605683492130770190',
     "url": 'https://www.tiktok.com/@olesamhain/video/7605683492130770190',
     "title": 'Bogey Ball: Halloween 1923 (2024) Full video',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7605683492130770190.jpg',
     "posted": 'Feb 11, 2026'},
    {"video_id": '7603568134280252686',
     "url": 'https://www.tiktok.com/@olesamhain/video/7603568134280252686',
     "title": 'Scarecrow from 2024',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7603568134280252686.jpg',
     "posted": 'Feb 6, 2026'},
    {"video_id": '7603390005553286414',
     "url": 'https://www.tiktok.com/@olesamhain/video/7603390005553286414',
     "title": 'The VVitch',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7603390005553286414.jpg',
     "posted": 'Feb 5, 2026'},
    {"video_id": '7603152982485536013',
     "url": 'https://www.tiktok.com/@olesamhain/video/7603152982485536013',
     "title": 'In the basement touching up a few things',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7603152982485536013.jpg',
     "posted": 'Feb 4, 2026'},
    {"video_id": '7602119695956757773',
     "url": 'https://www.tiktok.com/@olesamhain/video/7602119695956757773',
     "title": 'Scarecrow at Pawling Farm in Valley Forge',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7602119695956757773.jpg',
     "posted": 'Feb 2, 2026'},
    {"video_id": '7601997379692186893',
     "url": 'https://www.tiktok.com/@olesamhain/video/7601997379692186893',
     "title": 'Halloween 1923 (2024)',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7601997379692186893.jpg',
     "posted": 'Feb 1, 2026'},
    {"video_id": '7601349962860973326',
     "url": 'https://www.tiktok.com/@olesamhain/video/7601349962860973326',
     "title": 'HELL IS REAL Halloween 2025: INFERNO',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7601349962860973326.jpg',
     "posted": 'Jan 31, 2026'},
    {"video_id": '7601341568146083086',
     "url": 'https://www.tiktok.com/@olesamhain/video/7601341568146083086',
     "title": 'Scarecrow Country',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7601341568146083086.jpg',
     "posted": 'Jan 31, 2026'},
    {"video_id": '7601320379285622071',
     "url": 'https://www.tiktok.com/@olesamhain/video/7601320379285622071',
     "title": 'Dark Waters',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7601320379285622071.jpg',
     "posted": 'Jan 31, 2026'},
    {"video_id": '7601161053040430350',
     "url": 'https://www.tiktok.com/@olesamhain/video/7601161053040430350',
     "title": 'Disemboweled',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7601161053040430350.jpg',
     "posted": 'Jan 30, 2026'},
    {"video_id": '7600937178910297358',
     "url": 'https://www.tiktok.com/@olesamhain/video/7600937178910297358',
     "title": 'Halloween 2023: American Witchcraft',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7600937178910297358.jpg',
     "posted": 'Jan 29, 2026'},
    {"video_id": '7600796214719827214',
     "url": 'https://www.tiktok.com/@olesamhain/video/7600796214719827214',
     "title": 'In the workshop, have a lot of props I’m working on for a photoshoot that I’ll be doing once the snow is gone',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7600796214719827214.jpg',
     "posted": 'Jan 29, 2026'},
    {"video_id": '7600791655037357326',
     "url": 'https://www.tiktok.com/@olesamhain/video/7600791655037357326',
     "title": 'Halloween 2023: AMERICAN WITCHCRAFT',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7600791655037357326.jpg',
     "posted": 'Jan 29, 2026'},
    {"video_id": '7600790639260847373',
     "url": 'https://www.tiktok.com/@olesamhain/video/7600790639260847373',
     "title": 'The Hag — an old witch prop I made, just to photograph',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7600790639260847373.jpg',
     "posted": 'Jan 29, 2026'},
    {"video_id": '7600591056786296095',
     "url": 'https://www.tiktok.com/@olesamhain/video/7600591056786296095',
     "title": 'Hallowe’en 1923: BOGEY BALL (2024)',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7600591056786296095.jpg',
     "posted": 'Jan 29, 2026'},
    {"video_id": '7600589949964012831',
     "url": 'https://www.tiktok.com/@olesamhain/video/7600589949964012831',
     "title": 'Halloween 2025: INFERNO',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7600589949964012831.jpg',
     "posted": 'Jan 29, 2026'},
    {"video_id": '7600588803157396767',
     "url": 'https://www.tiktok.com/@olesamhain/video/7600588803157396767',
     "title": 'The Olde Cemetery',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7600588803157396767.jpg',
     "posted": 'Jan 29, 2026'},
    {"video_id": '7600575764773260574',
     "url": 'https://www.tiktok.com/@olesamhain/video/7600575764773260574',
     "title": 'HELL IS REAL',
     "creator": "@olesamhain",
     "cover": '/static/img/tt_ole_7600575764773260574.jpg',
     "posted": 'Jan 29, 2026'},
]


# Art in Motion (Dan, Oct 27, 2026): @chorenkids_events' Halloween
# character run — a Paris events crew's giant mascot costumes
# (Frankenstein's monster, Jack the Skeleton, zombies), embed-only via
# click-to-play facades on /fan-art (covers are each video's own
# frame, downloaded to static/img). The profile's Halloween 2026 set
# (14 videos, Oct 2-26) verified via the profile mirror on 2026-10-27;
# the rest of the catalogue is year-round party-mascot promos and was
# left off. Newest first.
ART_VIDEOS_CHOREN: list[dict] = [
    {"video_id": '7701046367187258657',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7701046367187258657',
     "title": "Les mascottes Halloween Zombie et Squelette débarquent pour vous faire frissonner",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7701046367187258657.jpg',
     "posted": 'Oct 26, 2026'},
    {"video_id": '7700503434461498656',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7700503434461498656',
     "title": "La mascotte du monstre de Frankenstein débarque pour Halloween !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7700503434461498656.jpg',
     "posted": 'Oct 25, 2026'},
    {"video_id": '7699896414393928993',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7699896414393928993',
     "title": "La mascotte Frankenstein débarque pour une animation Halloween monstrueusement amusante !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7699896414393928993.jpg',
     "posted": 'Oct 23, 2026'},
    {"video_id": '7699775444844907808',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7699775444844907808',
     "title": "Les mascottes Halloween débarquent pour une animation terriblement amusante !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7699775444844907808.jpg',
     "posted": 'Oct 23, 2026'},
    {"video_id": '7699184811230907680',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7699184811230907680',
     "title": "La mascotte Frankenstein débarque pour un Halloween monstrueusement amusant !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7699184811230907680.jpg',
     "posted": 'Oct 21, 2026'},
    {"video_id": '7698403837119384865',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7698403837119384865',
     "title": "La mascotte Zombie Halloween débarque pour faire frissonner vos événements !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7698403837119384865.jpg',
     "posted": 'Oct 19, 2026'},
    {"video_id": '7697954874251611425',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7697954874251611425',
     "title": "La mascotte Jack le Squelette débarque pour Halloween !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7697954874251611425.jpg',
     "posted": 'Oct 18, 2026'},
    {"video_id": '7697507993939840288',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7697507993939840288',
     "title": "Nos mascottes Halloween débarquent pour faire frissonner vos événements !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7697507993939840288.jpg',
     "posted": 'Oct 17, 2026'},
    {"video_id": '7696762916111977760',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7696762916111977760',
     "title": "La mascotte zombie vert débarque pour Halloween !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7696762916111977760.jpg',
     "posted": 'Oct 15, 2026'},
    {"video_id": '7696547043552152864',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7696547043552152864',
     "title": "La mascotte Frankenstein débarque pour Halloween !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7696547043552152864.jpg',
     "posted": 'Oct 14, 2026'},
    {"video_id": '7695311099058457889',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7695311099058457889',
     "title": "La mascotte Jack le squelette débarque pour une animation pleine de mystère !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7695311099058457889.jpg',
     "posted": 'Oct 11, 2026'},
    {"video_id": '7694946849546931489',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7694946849546931489',
     "title": "Les mascottes Squelette et Frankenstein débarquent pour Halloween !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7694946849546931489.jpg',
     "posted": 'Oct 10, 2026'},
    {"video_id": '7694740667414760736',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7694740667414760736',
     "title": "Les mascottes squelette et zombie débarquent pour Halloween !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7694740667414760736.jpg',
     "posted": 'Oct 9, 2026'},
    {"video_id": '7692079363574992161',
     "url": 'https://www.tiktok.com/@chorenkids_events/video/7692079363574992161',
     "title": "La mascotte Squelette débarque pour une animation Halloween terrifiante !",
     "creator": "@chorenkids_events",
     "cover": '/static/img/tt_chk_7692079363574992161.jpg',
     "posted": 'Oct 2, 2026'},
]


# ---------------------------------------------------------------- fan art

FANART_SQL = """CREATE TABLE IF NOT EXISTS fan_art (
    id INTEGER PRIMARY KEY,
    title TEXT NOT NULL,
    artist TEXT,
    town TEXT,
    media_path TEXT NOT NULL,
    thumb_path TEXT,
    votes INTEGER DEFAULT 0,
    approved INTEGER DEFAULT 0,
    created_at TEXT
)"""

def _ensure_fanart_cols(conn):
    """Idempotent migration: curated gallery pieces carry a source_url
    (e.g. the Wikimedia Commons file page) shown as a credit link."""
    cols = {r["name"] for r in conn.execute("PRAGMA table_info(fan_art)")}
    if "source_url" not in cols:
        conn.execute("ALTER TABLE fan_art ADD COLUMN source_url TEXT")


# Bundled starter examples (copied into the upload dir on first use) so the
# gallery is never empty at launch; clearly labeled as starter examples.
FANART_SEEDS = (
    ("fanart_seed1.jpg", "Pumpkin Nights"),
    ("fanart_seed2.jpg", "Haunted House on the Hill"),
)


def _seed_fanart(conn):
    if conn.execute("SELECT COUNT(*) FROM fan_art").fetchone()[0]:
        return
    for fname, title in FANART_SEEDS:
        src = BASE_DIR / "static" / "img" / fname
        if not src.exists():
            continue
        name = uuid.uuid4().hex
        media_rel = f"{name}.jpg"
        shutil.copy(src, UPLOAD_DIR / media_rel)
        try:
            thumb_rel = make_thumb(UPLOAD_DIR / media_rel, name)
        except (OSError, UnidentifiedImageError):
            thumb_rel = None
        conn.execute(
            "INSERT INTO fan_art (title, artist, town, media_path, thumb_path, votes, approved, created_at) "
            "VALUES (?, ?, ?, ?, ?, 0, 1, ?)",
            (title, "HauntMap starter example", None, media_rel, thumb_rel,
             datetime.now(timezone.utc).isoformat()),
        )


@app.get("/fan-art", response_class=HTMLResponse)
def fan_art(request: Request):
    voted = set()
    for part in request.cookies.get("fanart_votes", "").split(","):
        if part.strip().isdigit():
            voted.add(int(part.strip()))
    with get_conn(DB_PATH) as conn:
        conn.execute(FANART_SQL)
        _ensure_fanart_cols(conn)
        _seed_fanart(conn)
        rows = conn.execute(
            "SELECT * FROM fan_art WHERE approved = 1 ORDER BY votes DESC, id DESC"
        ).fetchall()
    pieces = []
    for r in rows:
        p = dict(r)
        p["media_url"] = f"/media/{p['media_path']}"
        p["thumb_url"] = f"/media/{p['thumb_path']}" if p.get("thumb_path") else p["media_url"]
        p["voted"] = p["id"] in voted
        pieces.append(p)
    return templates.TemplateResponse(
        request, "fan_art.html",
        {"pieces": pieces, "site_name": SITE_NAME,
         "art_videos": ART_VIDEOS,
         "art_videos_choren": ART_VIDEOS_CHOREN,
         "error": request.query_params.get("error"),
         "submitted": request.query_params.get("submitted")},
    )


@app.post("/fan-art/upload")
async def fanart_upload(
    title: str = Form(...),
    artist: str = Form(""),
    town: str = Form(""),
    source_url: str = Form(""),
    media: UploadFile = File(...),
):
    ext = safe_ext(media.filename or "")
    if ext not in PHOTO_EXTS:
        return RedirectResponse("/fan-art?error=Please+choose+an+image+(JPG,+PNG+or+WebP).", status_code=303)
    src = (source_url or "").strip()[:300]
    if not (src.startswith("https://") or src.startswith("http://")):
        src = None

    # Image decode + thumbnail and the insert run in the thread pool,
    # never on the event loop (blip hardening, Oct 25) — original flow.
    def _store() -> RedirectResponse:
        try:
            tmp = save_upload(media, MAX_PHOTO_BYTES)
            try:
                with Image.open(tmp) as im:
                    im.verify()
            except (UnidentifiedImageError, OSError):
                tmp.unlink(missing_ok=True)
                return RedirectResponse("/fan-art?error=That+file+isn%27t+a+readable+image.", status_code=303)
            name = uuid.uuid4().hex
            media_rel = f"{name}{ext}"
            shutil.move(tmp, UPLOAD_DIR / media_rel)
            try:
                thumb_rel = make_thumb(UPLOAD_DIR / media_rel, name)
            except (OSError, UnidentifiedImageError):
                (UPLOAD_DIR / media_rel).unlink(missing_ok=True)
                return RedirectResponse("/fan-art?error=Couldn%27t+process+that+image.", status_code=303)
        except ValueError:
            return RedirectResponse("/fan-art?error=That+image+is+too+large+(10+MB+max).", status_code=303)
        with get_conn(DB_PATH) as conn:
            conn.execute(FANART_SQL)
            _ensure_fanart_cols(conn)
            conn.execute(
                "INSERT INTO fan_art (title, artist, town, media_path, thumb_path, votes, approved, created_at, source_url) "
                "VALUES (?, ?, ?, ?, ?, 0, 0, ?, ?)",
                (title.strip()[:120], (artist or "").strip()[:60] or None,
                 (town or "").strip()[:80] or None, media_rel, thumb_rel,
                 datetime.now(timezone.utc).isoformat(), src),
            )
        # Submissions stay PENDING (approved = 0) until Dan approves in admin.
        return RedirectResponse("/fan-art?submitted=1", status_code=303)

    return await run_in_threadpool(_store)


@app.post("/fan-art/{fid}/vote")
def fanart_vote(fid: int, request: Request):
    voted = set()
    for part in request.cookies.get("fanart_votes", "").split(","):
        if part.strip().isdigit():
            voted.add(int(part.strip()))
    with get_conn(DB_PATH) as conn:
        conn.execute(FANART_SQL)
        row = conn.execute("SELECT votes FROM fan_art WHERE id = ? AND approved = 1", (fid,)).fetchone()
        if row is None:
            return JSONResponse({"error": "not found"}, status_code=404)
        votes = row["votes"]
        if fid in voted:
            votes = max(0, votes - 1)
            voted.discard(fid)
            now_voted = False
        else:
            votes += 1
            voted.add(fid)
            now_voted = True
        conn.execute("UPDATE fan_art SET votes = ? WHERE id = ?", (votes, fid))
    resp = JSONResponse({"votes": votes, "voted": now_voted})
    resp.set_cookie("fanart_votes", ",".join(str(v) for v in sorted(voted)),
                    max_age=60 * 60 * 24 * 120, path="/", samesite="lax")
    return resp


@app.post("/admin/fan-art/{fid}/approve")
def admin_fanart_approve(fid: int, request: Request):
    if not is_admin(request):
        return RedirectResponse("/admin", status_code=303)
    with get_conn(DB_PATH) as conn:
        conn.execute(FANART_SQL)
        _ensure_fanart_cols(conn)
        conn.execute("UPDATE fan_art SET approved = 1 WHERE id = ?", (fid,))
    return RedirectResponse("/admin", status_code=303)


@app.post("/admin/fan-art/{fid}/delete")
def admin_fanart_delete(fid: int, request: Request):
    if not is_admin(request):
        return RedirectResponse("/admin", status_code=303)
    with get_conn(DB_PATH) as conn:
        conn.execute(FANART_SQL)
        _ensure_fanart_cols(conn)
        row = conn.execute("SELECT media_path, thumb_path FROM fan_art WHERE id = ?", (fid,)).fetchone()
        if row:
            for rel in (row["media_path"], row["thumb_path"]):
                if rel:
                    (UPLOAD_DIR / rel).unlink(missing_ok=True)
            conn.execute("DELETE FROM fan_art WHERE id = ?", (fid,))
    return RedirectResponse("/admin", status_code=303)


# ---------------------------------------------------------------- admin

# ------------------------------------------------- per-page time (Oct 25)
# Dan's ask: how long people spend on EACH page, not just per visit.
# Built from the engaged-time beacon rows (Item 6): every row is an
# incremental delta of VISIBLE time on a path, stamped with the
# beacon's per-page-load pvid, so SUM(seconds) GROUP BY path, pvid
# reconstructs one page view's dwell. Views come from page_views
# (human-screened since Oct 27 — machine paths + machine user agents
# excluded — but still including sub-second and no-JS views the beacon
# never sees); avg = total attention / views. Median + quick-exit share are
# computed over the measured page views only (pvid groups) — a stay
# under ~1s sends no beacon at all, so the very fastest bounces are
# invisible to those two columns; the template says so in plain words.
# The aggregate sits behind _ttl_cached like every other hot admin
# aggregate (fortification pass 2) — an admin render never re-scans
# the analytics tables inline.
_PAGE_TIME_LABELS = {
    "/": "Home", "/events": "Events", "/map": "Map", "/nearby": "Nearby",
    "/tours": "Tours", "/watch": "Watch", "/leaderboard": "Top Haunts",
    "/leaderboard/states": "Top 10 by State",
    "/restaurhaunts": "Restaurhaunts", "/hauntsocial": "HauntSocial",
    "/chat": "Haunt Chat",
    "/games": "Games", "/diy": "DIY", "/diy-costumes": "DIY Costumes",
    "/movies": "Movies", "/music": "Music", "/markets": "Markets",
    "/pop-haunt-culture": "Pop Haunt Culture",
    "/passport": "Haunt Passport", "/daily": "Daily Fright",
    "/about": "About Us", "/advertise": "Advertise",
    "/signup": "Sign Up", "/login": "Log In",
}


def _fmt_attention(sec: float) -> str:
    """Humanized total-attention: 45s / 3m 20s / 2h 05m."""
    sec = int(round(sec))
    if sec < 60:
        return f"{sec}s"
    if sec < 3600:
        return f"{sec // 60}m {sec % 60:02d}s"
    return f"{sec // 3600}h {(sec % 3600) // 60:02d}m"


def _page_time_build() -> list:
    rows_out: list = []
    # Views are HUMAN views (Oct 27): the machine-UA screen joins the
    # long-standing machine-path exclusions, so a crawler fetching a
    # page no longer inflates the denominator its (zero) attention is
    # averaged over. The beacon side needs no screen — its rows only
    # exist when a real browser ran the page's timer.
    frag, frag_params = _machine_ua_sql()
    with get_conn(DB_PATH) as conn:
        cand = conn.execute(
            "SELECT path, COUNT(*) AS views FROM page_views "
            "WHERE viewed_at >= datetime('now', '-7 days') "
            # Infrastructure paths are not pages anyone spends time on
            # (the health check alone would hold a top slot forever),
            # and neither are /api/* JSON endpoints.
            "AND path NOT IN ('/healthz', '/favicon.ico', '/robots.txt', "
            "'/sitemap.xml') AND path NOT LIKE '/api/%' "
            f"AND {frag} "
            "GROUP BY path ORDER BY views DESC LIMIT 40", frag_params).fetchall()
        if not cand:
            return rows_out
        paths = [r["path"] for r in cand]
        marks = ",".join("?" * len(paths))
        att = {r["path"]: (r["secs"] or 0) for r in conn.execute(
            "SELECT path, SUM(seconds) AS secs FROM engagement_events "
            "WHERE event = 'engaged' "
            "AND created_at >= datetime('now', '-7 days') "
            f"AND path IN ({marks}) GROUP BY path", paths)}
        dwell: dict = {}
        for r in conn.execute(
                "SELECT path, SUM(seconds) AS secs FROM engagement_events "
                "WHERE event = 'engaged' AND pvid IS NOT NULL "
                "AND created_at >= datetime('now', '-7 days') "
                f"AND path IN ({marks}) GROUP BY path, pvid", paths):
            dwell.setdefault(r["path"], []).append(r["secs"] or 0)
        pin_ids = [int(p[3:]) for p in paths
                   if p.startswith("/d/") and p[3:].isdigit()]
        pins: dict = {}
        if pin_ids:
            pm = ",".join("?" * len(pin_ids))
            for r in conn.execute(
                    f"SELECT id, title, town FROM entries WHERE id IN ({pm})",
                    pin_ids):
                pins[r["id"]] = r
    for r in cand:
        path, views = r["path"], r["views"]
        total_secs = att.get(path, 0)
        ds = sorted(dwell.get(path, []))
        n = len(ds)
        median = 0.0
        if n:
            mid = n // 2
            median = ds[mid] if n % 2 else (ds[mid - 1] + ds[mid]) / 2
        label = _PAGE_TIME_LABELS.get(path)
        if label is None and path.startswith("/d/") and path[3:].isdigit():
            e = pins.get(int(path[3:]))
            label = (f"#{path[3:]} {e['title']}" if e and e["title"]
                     else f"Pin {path[3:]}")
            if e and e["town"]:
                label += f" · {e['town']}"
        rows_out.append({
            "path": path, "label": label or path, "views": views,
            "avg_s": _fmt_dur_admin(total_secs / views) if views else "0s",
            "median_s": _fmt_dur_admin(median) if n else None,
            "total_s": _fmt_attention(total_secs),
            "measured": n,
            "quick": (sum(1 for d in ds if d < 5) / n * 100) if n else None,
        })
    return rows_out


def _fmt_dur_admin(sec: float) -> str:
    sec = int(round(sec))
    return f"{sec}s" if sec < 60 else f"{sec // 60}m {sec % 60:02d}s"


def _page_time_stats() -> list:
    return _ttl_cached("admin:page_time", _page_time_build)


# ------------------------------------------------- US states (Oct 27)
# Dan's ask: which U.S. states are visiting — the whole map, not a
# top-20. Built from page_views geography: country has flowed from
# Cloudflare on every proxied view since Oct 26, but region (state)
# only arrives with CF's visitor-location transform (off today), so
# since Oct 27 the analytics writer ALSO resolves the state from the
# view's stored IP against the bundled GeoLite2 database
# (geo_src marks which source each row's state came from). Counts are
# HUMAN views only — the sponsor figures' machine-path screen
# (_MK_HUMAN) plus the machine-UA screen (_machine_ua_sql) — and the
# coverage block states plainly how many U.S. views carry a state at
# all, so a thin table can never masquerade as the whole audience.
# TTL-cached like the other admin aggregates.

def _us_states_build() -> dict:
    frag, frag_params = _machine_ua_sql()
    human = f"{_MK_HUMAN} AND {frag}"
    win7 = "viewed_at >= datetime('now', '-7 days')"
    out = {"rows": [], "unknown": None, "coverage": {}}
    with get_conn(DB_PATH) as conn:
        def _count(where: str) -> int:
            return conn.execute(
                f"SELECT COUNT(*) FROM page_views WHERE {where}",
                frag_params).fetchone()[0]

        known_views = _count(
            f"{human} AND country = 'US' "
            "AND region IS NOT NULL AND region != ''")
        cov = {
            "total_human": _count(human),
            "with_country": _count(
                f"{human} AND country IS NOT NULL AND country != ''"),
            "us_views": _count(f"{human} AND country = 'US'"),
            "state_known_views": known_views,
            "cf_views": 0, "ip_views": 0,
        }
        for r in conn.execute(
                "SELECT geo_src, COUNT(*) AS n FROM page_views "
                f"WHERE {human} AND country = 'US' "
                "AND region IS NOT NULL AND region != '' "
                "GROUP BY geo_src", frag_params):
            if r["geo_src"] == "cf":
                cov["cf_views"] = r["n"]
            elif r["geo_src"] == "ip":
                cov["ip_views"] = r["n"]
        agg_sql = (
            "SELECT COUNT(DISTINCT sid) AS visitors, COUNT(*) AS views, "
            "COUNT(DISTINCT CASE WHEN {w} THEN sid END) AS visitors7, "
            "SUM(CASE WHEN {w} THEN 1 ELSE 0 END) AS views7 "
            "FROM page_views WHERE {cond}")
        unk = conn.execute(
            agg_sql.format(w=win7, cond=(
                f"{human} AND country = 'US' "
                "AND (region IS NULL OR region = '')")),
            frag_params).fetchone()
        if unk and unk["views"]:
            out["unknown"] = {
                "visitors": unk["visitors"], "views": unk["views"],
                "visitors7": unk["visitors7"], "views7": unk["views7"]}
        merged: dict = {}
        for r in conn.execute(
                "SELECT region, COUNT(DISTINCT sid) AS visitors, "
                "COUNT(*) AS views, "
                f"COUNT(DISTINCT CASE WHEN {win7} THEN sid END) "
                "AS visitors7, "
                f"SUM(CASE WHEN {win7} THEN 1 ELSE 0 END) AS views7 "
                f"FROM page_views WHERE {human} AND country = 'US' "
                "AND region IS NOT NULL AND region != '' "
                "GROUP BY region", frag_params):
            # Stored regions are already state codes when resolvable,
            # but a raw CF region name can survive as a fallback —
            # normalize both shapes to the code before grouping.
            code = _state_code_from_region(r["region"], "") or "??"
            m = merged.setdefault(code, {"visitors": 0, "views": 0,
                                         "visitors7": 0, "views7": 0})
            m["visitors"] += r["visitors"]
            m["views"] += r["views"]
            m["visitors7"] += r["visitors7"]
            m["views7"] += r["views7"] or 0
    rows = []
    for code, m in merged.items():
        name = US_STATE_NAMES.get(code)
        rows.append({
            "code": code,
            "label": (f"{name} ({code})" if name else
                      "Unrecognized region label"),
            **m,
            "share": (round(m["views"] / known_views * 100, 1)
                      if known_views else 0.0),
        })
    rows.sort(key=lambda x: (-x["visitors"], -x["views"], x["label"]))
    cov["known_pct"] = (round(known_views / cov["us_views"] * 100, 1)
                        if cov["us_views"] else 0.0)
    out["rows"] = rows
    out["coverage"] = cov
    return out


def _us_states_stats() -> dict:
    return _ttl_cached("admin:us_states", _us_states_build)


@app.get("/admin", response_class=HTMLResponse)
def admin(request: Request):
    if not is_admin(request):
        return templates.TemplateResponse(request, "admin.html", {"request": request, "logged_in": False, "error": None}
        )
    with get_conn(DB_PATH) as conn:
        flagged = [row_to_dict(r) for r in conn.execute(
            "SELECT * FROM entries WHERE flagged = 1 ORDER BY created_at DESC").fetchall()]
        all_entries = [row_to_dict(r) for r in conn.execute(
            "SELECT * FROM entries ORDER BY created_at DESC LIMIT 200").fetchall()]
        subs = conn.execute(
            "SELECT email, location, created_at FROM subscribers ORDER BY created_at DESC").fetchall()
        sub_count = len(subs)
        conn.execute(TOWN_REQUESTS_TABLE_SQL)
        town_reqs = conn.execute(
            "SELECT email, town, state, zip, created_at FROM town_requests "
            "ORDER BY created_at DESC LIMIT 100").fetchall()
        town_req_count = conn.execute(
            "SELECT COUNT(*) FROM town_requests").fetchone()[0]
        conn.execute(FEEDBACK_TABLE_SQL)
        feedback_rows = [dict(r) for r in conn.execute(
            "SELECT * FROM feedback ORDER BY created_at DESC LIMIT 100").fetchall()]
        for f in feedback_rows:
            f["category_label"] = FEEDBACK_CATEGORIES.get(
                f.get("category") or "other", "🎃 Other")
        feedback_count = conn.execute(
            "SELECT COUNT(*) FROM feedback").fetchone()[0]
        conn.execute(FANART_SQL)
        fanart_pending = [dict(r) for r in conn.execute(
            "SELECT * FROM fan_art WHERE approved = 0 ORDER BY created_at DESC").fetchall()]
        fanart_live = [dict(r) for r in conn.execute(
            "SELECT * FROM fan_art WHERE approved = 1 ORDER BY created_at DESC").fetchall()]
        for p in fanart_pending + fanart_live:
            p["thumb_url"] = (f"/media/{p['thumb_path']}" if p.get("thumb_path")
                              else f"/media/{p['media_path']}")
    return templates.TemplateResponse(request, "admin.html",
        {"request": request, "logged_in": True, "flagged": flagged,
         "all_entries": all_entries, "subs": subs, "sub_count": sub_count, "error": None,
         "town_reqs": town_reqs, "town_req_count": town_req_count,
         "feedback_rows": feedback_rows, "feedback_count": feedback_count,
         "fanart_pending": fanart_pending, "fanart_live": fanart_live},
    )


@app.get("/admin/stats", response_class=HTMLResponse)
def admin_stats(request: Request):
    """Traffic dashboard: page views by day and top pages."""
    if not is_admin(request):
        return RedirectResponse("/admin", status_code=303)
    with get_conn(DB_PATH) as conn:
        total = conn.execute("SELECT COUNT(*) FROM page_views").fetchone()[0]
        today = conn.execute(
            "SELECT COUNT(*) FROM page_views WHERE date(viewed_at) = date('now')").fetchone()[0]
        week = conn.execute(
            "SELECT COUNT(*) FROM page_views WHERE viewed_at >= datetime('now', '-7 days')").fetchone()[0]
        by_day = conn.execute(
            "SELECT date(viewed_at) AS day, COUNT(*) AS views "
            "FROM page_views GROUP BY day ORDER BY day DESC LIMIT 14").fetchall()
        top_pages = conn.execute(
            "SELECT path, COUNT(*) AS views FROM page_views "
            "GROUP BY path ORDER BY views DESC LIMIT 20").fetchall()
        top_referrers = conn.execute(
            "SELECT CASE WHEN referrer = '' OR referrer IS NULL THEN '(direct)' "
            "ELSE referrer END AS ref, COUNT(*) AS views FROM page_views "
            "GROUP BY ref ORDER BY views DESC LIMIT 15").fetchall()
        by_device = conn.execute(
            "SELECT CASE WHEN device = '' OR device IS NULL THEN 'Unknown' "
            "ELSE device END AS dev, COUNT(*) AS views FROM page_views "
            "GROUP BY dev ORDER BY views DESC").fetchall()
        # --- visitors by geography (Dan, Oct 26): where the audience
        # actually is. Counted BOTH ways and labelled on the page:
        # visitors = COUNT(DISTINCT sid) (one person counts once per
        # place), views = raw page views, matching the panels above.
        # Geo columns exist only on views recorded since
        # _GEO_COLLECTING_SINCE — every query below filters to rows
        # that carry a value, so nothing here implies older coverage.
        # City rows exist only once Cloudflare's visitor-location
        # transform is on; state rows (the _us_states_stats table
        # below this panel) additionally come from the writer's IP
        # lookup since Oct 27, transform or not.
        geo = {"countries": [], "cities": []}
        for r in conn.execute(
                "SELECT country, COUNT(DISTINCT sid) AS visitors, "
                "COUNT(*) AS views FROM page_views "
                "WHERE country IS NOT NULL AND country != '' "
                "GROUP BY country ORDER BY visitors DESC, views DESC "
                "LIMIT 20"):
            geo["countries"].append({
                "code": r["country"],
                "label": _COUNTRY_NAMES.get(r["country"], r["country"]),
                "visitors": r["visitors"], "views": r["views"]})
        # US states moved to _us_states_stats() (Oct 27): the full
        # human-only state table with 7-day + all-time windows, share
        # and an explicit coverage block — see its section comment.
        for r in conn.execute(
                "SELECT city, region, country, COUNT(DISTINCT sid) AS visitors, "
                "COUNT(*) AS views FROM page_views "
                "WHERE city IS NOT NULL AND city != '' "
                "GROUP BY city, region, country "
                "ORDER BY visitors DESC, views DESC LIMIT 20"):
            label = r["city"]
            if r["region"]:
                label += f", {r['region']}"
            if r["country"] and r["country"] != "US":
                label += f" ({r['country']})"
            geo["cities"].append({
                "label": label,
                "visitors": r["visitors"], "views": r["views"]})
        # --- engagement events (Wave 2, Item 2): last 7 days ---
        # (engagement_events is created by init_db at startup — no DDL here.)
        eng_counts = {ev: 0 for ev in ENGAGEMENT_EVENTS_ALL}
        for r in conn.execute(
                "SELECT event, COUNT(*) AS n FROM engagement_events "
                "WHERE created_at >= datetime('now', '-7 days') GROUP BY event"):
            eng_counts[r["event"]] = r["n"]
        eng_with_pin = conn.execute(
            "SELECT COUNT(*) FROM engagement_events WHERE entry_id IS NOT NULL "
            "AND created_at >= datetime('now', '-7 days')").fetchone()[0]
        pin_views_week = conn.execute(
            "SELECT COUNT(*) FROM page_views WHERE path LIKE '/d/%' "
            "AND viewed_at >= datetime('now', '-7 days')").fetchone()[0]
        eng_top_pins = conn.execute(
            "SELECT g.entry_id AS entry_id, COUNT(*) AS n, "
            "e.title AS title, e.town AS town FROM engagement_events g "
            "LEFT JOIN entries e ON e.id = g.entry_id "
            "WHERE g.entry_id IS NOT NULL "
            "AND g.created_at >= datetime('now', '-7 days') "
            "GROUP BY g.entry_id ORDER BY n DESC, g.entry_id ASC LIMIT 5").fetchall()
        # --- Rail Boost (Oct 25): per-rail clicks vs impressions —
        # CTR per rail SEEN (impression = rail >=50% visible once per
        # page view), not per page view. rail_click rows from before
        # per-rail attribution carry source NULL -> '(unattributed)'.
        rail_rows = conn.execute(
            "SELECT COALESCE(source, '(unattributed)') AS src, "
            "SUM(CASE WHEN event = 'rail_click' THEN 1 ELSE 0 END) AS clicks, "
            "SUM(CASE WHEN event = 'rail_impression' THEN 1 ELSE 0 END) AS imps "
            "FROM engagement_events "
            "WHERE event IN ('rail_click', 'rail_impression') "
            "AND created_at >= datetime('now', '-7 days') "
            "GROUP BY src ORDER BY clicks DESC, imps DESC").fetchall()
        eng_rail_sources = [
            {"src": r["src"], "clicks": r["clicks"], "imps": r["imps"],
             "ctr": (r["clicks"] / r["imps"]) if r["imps"] else None}
            for r in rail_rows]
        engagement = {
            "counts": [(ev, eng_counts[ev]) for ev in ENGAGEMENT_EVENTS_ALL],
            "rail_sources": eng_rail_sources,
            "total": sum(eng_counts.values()),
            "with_pin": eng_with_pin,
            "pin_views": pin_views_week,
            "ratio": (eng_with_pin / pin_views_week) if pin_views_week else 0,
            "top_pins": eng_top_pins,
        }
        # --- visit duration: sessionize page views per visitor (30-min window) ---
        srows = conn.execute(
            "SELECT sid, viewed_at FROM page_views WHERE sid IS NOT NULL "
            "AND viewed_at >= datetime('now', '-30 days') ORDER BY sid, viewed_at").fetchall()
    visits_list = []
    cur_sid, cur_times = None, []

    def _flush_visit():
        if cur_times:
            visits_list.append(((cur_times[-1] - cur_times[0]).total_seconds(), len(cur_times)))

    for r in srows:
        t = datetime.fromisoformat(r["viewed_at"])
        if r["sid"] != cur_sid or (cur_times and (t - cur_times[-1]).total_seconds() > 1800):
            _flush_visit()
            cur_sid, cur_times = r["sid"], []
        cur_times.append(t)
    _flush_visit()

    def _fmt_dur(sec):
        sec = int(round(sec))
        return f"{sec}s" if sec < 60 else f"{sec // 60}m {sec % 60:02d}s"

    n_visits = len(visits_list)
    if n_visits:
        durs = sorted(d for d, _ in visits_list)
        multi = [d for d, p in visits_list if p > 1]
        mid = n_visits // 2
        median_dur = durs[mid] if n_visits % 2 else (durs[mid - 1] + durs[mid]) / 2
        bucket_defs = [("<10 sec", 0, 10), ("10–60 sec", 10, 60), ("1–3 min", 60, 180),
                       ("3–5 min", 180, 300), ("5–10 min", 300, 600), ("10+ min", 600, float("inf"))]
        duration = {
            "visits": n_visits,
            "avg": _fmt_dur(sum(durs) / n_visits),
            "median": _fmt_dur(median_dur),
            "engaged_avg": _fmt_dur(sum(multi) / len(multi)) if multi else "0s",
            "bounce": round(sum(1 for _, p in visits_list if p == 1) / n_visits * 100, 1),
            "avg_pages": round(sum(p for _, p in visits_list) / n_visits, 1),
            "buckets": [(label, sum(1 for d in durs if lo <= d < hi)) for label, lo, hi in bucket_defs],
        }
    else:
        duration = {"visits": 0, "avg": "—", "median": "—", "engaged_avg": "—",
                    "bounce": 0, "avg_pages": 0, "buckets": []}
    return templates.TemplateResponse(request, "stats.html",
        {"request": request, "total": total, "today": today, "week": week,
         "by_day": by_day, "top_pages": top_pages,
         "top_referrers": top_referrers, "by_device": by_device,
         "duration": duration, "engagement": engagement,
         "geo": geo, "geo_since": _GEO_COLLECTING_SINCE,
         "us_states": _us_states_stats(),
         "ip_geo_since": _IP_GEO_COLLECTING_SINCE,
         "page_time": _page_time_stats()})


@app.post("/admin/login", response_class=HTMLResponse)
def admin_login(request: Request, password: str = Form("")):
    if secrets.compare_digest(password, ADMIN_PASSWORD):
        token = secrets.token_urlsafe(32)
        admin_sessions.add(token)
        resp = RedirectResponse("/admin", status_code=303)
        resp.set_cookie(ADMIN_COOKIE, token, httponly=True, samesite="lax",
                        max_age=12 * 3600)
        return resp
    return templates.TemplateResponse(request, "admin.html",
        {"request": request, "logged_in": False, "error": "Wrong password."},
        status_code=401,
    )


@app.post("/admin/logout")
def admin_logout(request: Request):
    admin_sessions.discard(request.cookies.get(ADMIN_COOKIE, ""))
    resp = RedirectResponse("/admin", status_code=303)
    resp.delete_cookie(ADMIN_COOKIE)
    return resp


class _ZipStreamSink:
    """Non-seekable file-like sink zipfile writes into while streaming.

    Bytes land in a small buffer that the response generator drains after
    every source chunk, so memory stays bounded no matter how large the
    archive grows. tell() tracks total bytes written (zipfile needs it for
    header offsets); with seekable() False, zipfile emits a data descriptor
    per entry instead of seeking back to patch the local header.
    """

    def __init__(self):
        self._buf = bytearray()
        self._pos = 0

    def write(self, data):
        self._buf += data
        self._pos += len(data)
        return len(data)

    def tell(self):
        return self._pos

    def seekable(self):
        return False

    def flush(self):
        pass

    def drain(self):
        chunk = bytes(self._buf)
        self._buf.clear()
        return chunk


def _backup_zip_chunks():
    """Yield the backup zip (database + all uploads) as it is generated.

    Same archive layout as the old temp-file version: hauntmap.db first,
    then uploads/<path> for every file under UPLOAD_DIR, in sorted order.
    Entries are ZIP_STORED — the payloads are already-compressed media, so
    storing costs almost no CPU — and source files are copied through in
    256 KB chunks, so even a large video never lands in RAM whole.
    """
    sink = _ZipStreamSink()
    # WAL mode (blip hardening, Oct 25): recently committed rows live in
    # the hauntmap.db-wal sidecar until a checkpoint folds them into the
    # main file. Checkpoint first, or the raw file copy below would
    # silently miss the newest data.
    try:
        with get_conn(DB_PATH) as conn:
            conn.execute("PRAGMA wal_checkpoint(TRUNCATE)")
    except Exception:
        pass  # backup proceeds with whatever is already in the main file
    files = []
    if DB_PATH.exists():
        files.append((DB_PATH, "hauntmap.db"))
    if UPLOAD_DIR.exists():
        for f in sorted(UPLOAD_DIR.rglob("*")):
            if f.is_file():
                files.append((f, f"uploads/{f.relative_to(UPLOAD_DIR)}"))
    with zipfile.ZipFile(sink, "w", zipfile.ZIP_STORED) as z:
        for path, arcname in files:
            zinfo = zipfile.ZipInfo.from_file(path, arcname)
            with z.open(zinfo, "w") as dest, open(path, "rb") as src:
                while chunk := src.read(256 * 1024):
                    dest.write(chunk)
                    data = sink.drain()
                    if data:
                        yield data
            data = sink.drain()
            if data:
                yield data
    data = sink.drain()
    if data:
        yield data


@app.get("/admin/backup")
def admin_backup(request: Request):
    """Download a zip of the database + all uploads (for automated backups). Admin only.

    Streamed: the archive is generated on the fly into the response. The old
    version built the whole ~2 GB zip as a temp file first — Render's /tmp
    is capped at 2 GB, so once the backup grew past it a backup run filled
    /tmp and Render killed the instance (Oct 24 outage). No temp file and
    no Content-Length now: the response is chunked.
    """
    if not is_admin(request):
        raise HTTPException(401, "Not authorized.")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%d")
    return StreamingResponse(
        _backup_zip_chunks(),
        media_type="application/zip",
        headers={"Content-Disposition":
                 f'attachment; filename="hauntmap-backup-{stamp}.zip"'},
    )


@app.post("/admin/rethumb")
def admin_rethumb(request: Request, offset: int = 0, limit: int = 200):
    """Recompress existing thumbnails in place to the 4:3 / 800px / q76 spec
    (older thumbs were uncropped 640px q80 — nearly as heavy as originals).
    Chunked and resumable: call with increasing offset until done=true.
    Only replaces a file when the new version is smaller. Admin only."""
    _require_admin(request)
    files = sorted(THUMB_DIR.glob("*.jpg"))
    batch = files[offset:offset + limit]
    before = after = shrunk = 0
    for f in batch:
        try:
            old = f.stat().st_size
            tmp = f.with_suffix(".rethmb")
            with Image.open(f) as im:
                im.load()
                _write_thumb(im, tmp)
            new = tmp.stat().st_size
            if new < old:
                tmp.replace(f)
                make_card_variant(f)  # keep the Item 10 card variant in sync
                shrunk += 1
            else:
                tmp.unlink(missing_ok=True)
                new = old
            before += old
            after += new
        except (OSError, UnidentifiedImageError):
            continue
    return {"total": len(files), "offset": offset, "processed": len(batch),
            "shrunk": shrunk, "bytes_before": before, "bytes_after": after,
            "done": offset + len(batch) >= len(files)}


@app.post("/admin/recap")
def admin_recap(request: Request, offset: int = 0, limit: int = 100):
    """Apply the 1920px original cap to already-stored entry photos (detail
    pages serve originals; early phone uploads are 1.3-1.8 MB). Same chunked,
    resumable pattern as /admin/rethumb. Videos untouched. Admin only."""
    _require_admin(request)
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT media_path FROM entries WHERE media_type = 'photo' "
            "AND media_path != '' ORDER BY id").fetchall()
    paths = [r["media_path"] for r in rows]
    batch = paths[offset:offset + limit]
    before = after = shrunk = 0
    for rel in batch:
        f = UPLOAD_DIR / rel
        if not f.exists():
            continue
        try:
            old = f.stat().st_size
            _cap_original(f)
            _recompress_jpeg(f)
            new = f.stat().st_size
            if new < old:
                shrunk += 1
            before += old
            after += new
        except OSError:
            continue
    return {"total": len(paths), "offset": offset, "processed": len(batch),
            "shrunk": shrunk, "bytes_before": before, "bytes_after": after,
            "done": offset + len(batch) >= len(paths)}


@app.post("/admin/fix-orientation")
def admin_fix_orientation(request: Request, offset: int = 0, limit: int = 100):
    """Sweep stored entry photos for EXIF-sideways originals: transpose the
    pixels upright, strip the flag, and regenerate the thumbnail from the
    fixed original. Same chunked, resumable pattern as /admin/recap.
    Admin only. (Dan Oct 22: pictures must ALWAYS display right side up.)"""
    _require_admin(request)
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT id, media_path, thumb_path FROM entries "
            "WHERE media_type = 'photo' AND media_path != '' ORDER BY id").fetchall()
    batch = rows[offset:offset + limit]
    fixed = []
    for r in batch:
        f = UPLOAD_DIR / r["media_path"]
        if not f.exists():
            continue
        try:
            if _normalize_orientation(f):
                fixed.append(r["id"])
                if r["thumb_path"]:
                    thumb = UPLOAD_DIR / r["thumb_path"]
                    if thumb.exists():
                        with Image.open(f) as im:
                            im.load()
                            _write_thumb(im, thumb)
                        make_card_variant(thumb)
        except (OSError, UnidentifiedImageError):
            continue
    return {"total": len(rows), "offset": offset, "processed": len(batch),
            "fixed_ids": fixed, "done": offset + len(batch) >= len(rows)}


def _require_admin(request: Request) -> None:
    if not is_admin(request):
        raise HTTPException(403, "Admin only.")


@app.post("/admin/hide/{entry_id}")
def admin_hide(entry_id: int, request: Request):
    _require_admin(request)
    with get_conn(DB_PATH) as conn:
        conn.execute("UPDATE entries SET hidden = 1 WHERE id = ?", (entry_id,))
        conn.commit()
    return RedirectResponse("/admin", status_code=303)


@app.post("/admin/unhide/{entry_id}")
def admin_unhide(entry_id: int, request: Request):
    _require_admin(request)
    with get_conn(DB_PATH) as conn:
        conn.execute("UPDATE entries SET hidden = 0, flagged = 0 WHERE id = ?", (entry_id,))
        conn.commit()
    return RedirectResponse("/admin", status_code=303)


@app.post("/admin/delete/{entry_id}")
def admin_delete(entry_id: int, request: Request):
    _require_admin(request)
    entry = get_entry(entry_id)
    if entry:
        for rel in {entry["media_path"], entry.get("thumb_path")}:
            if rel:
                (UPLOAD_DIR / rel).unlink(missing_ok=True)
        if entry.get("thumb_path"):  # Item 10 card variant, if any
            (CARD_THUMB_DIR / Path(entry["thumb_path"]).name).unlink(missing_ok=True)
        with get_conn(DB_PATH) as conn:
            conn.execute("DELETE FROM entries WHERE id = ?", (entry_id,))
            conn.commit()
    return RedirectResponse("/admin", status_code=303)


@app.post("/admin/tag/{entry_id}")
async def admin_tag(entry_id: int, request: Request):
    """Update scare_level and tags for an entry (admin)."""
    _require_admin(request)
    form = await request.form()
    scare = form.get("scare_level", "")
    scare = scare if scare in ("family", "spooky", "creepy", "terrifying", "extreme") else None
    tags = ",".join(sorted({t for t in form.getlist("tags")
                            if t in ("animatronics", "inflatables", "handmade", "walkthrough",
                                     "projector", "lights", "music", "street-wide",
                                     "multi-house", "ticketed", "2025", "market", "oddities", "witchy", "craft", "flea", "free", "flagship", "21+")})) or None
    category = form.get("category", "")
    category = category if category in CATEGORIES else None
    with get_conn(DB_PATH) as conn:
        if category:
            conn.execute("UPDATE entries SET scare_level = ?, tags = ?, category = ? WHERE id = ?",
                         (scare, tags, category, entry_id))
        else:
            conn.execute("UPDATE entries SET scare_level = ?, tags = ? WHERE id = ?",
                         (scare, tags, entry_id))
        conn.commit()
    return RedirectResponse("/admin", status_code=303)


@app.post("/admin/edit/{entry_id}")
async def admin_edit(entry_id: int, request: Request):
    """Update title, town label, verified street address, TikTok URL, events facets (admin).

    Only fields present in the form are touched. `address` may be sent
    empty to clear it back to NULL; title/town must be non-empty when sent.
    Built for the Oct 2026 verified-address cleanup (near-miss town-label
    corrections + storing geocode-verified addresses for bucket-B pins).
    """
    _require_admin(request)
    form = await request.form()
    updates: dict[str, str | None] = {}
    for field in ("title", "town"):
        if field in form:
            value = str(form.get(field, "")).strip()
            if not value:
                return JSONResponse({"error": f"{field} must not be empty"}, status_code=400)
            updates[field] = value
    if "address" in form:
        addr = str(form.get("address", "")).strip()
        updates["address"] = addr or None
    if "tiktok_url" in form:
        tt = str(form.get("tiktok_url", "")).strip()
        if tt and "tiktok.com" not in tt:
            return JSONResponse({"error": "tiktok_url must be a TikTok URL"}, status_code=400)
        updates["tiktok_url"] = tt or None
    # Events facets: validated against the taxonomy; empty clears to NULL.
    for field, valid in (("ev_type", EVENT_TYPES), ("ev_genre", EVENT_GENRES),
                         ("ev_venue", EVENT_VENUES)):
        if field in form:
            value = str(form.get(field, "")).strip()
            if value and value not in valid:
                return JSONResponse(
                    {"error": f"{field} must be one of: {', '.join(valid)}"},
                    status_code=400)
            updates[field] = value or None
    if not updates:
        return JSONResponse({"error": "No fields to update"}, status_code=400)
    if not get_entry(entry_id):
        return JSONResponse({"error": "No such entry"}, status_code=404)
    set_sql = ", ".join(f"{k} = ?" for k in updates)
    with get_conn(DB_PATH) as conn:
        conn.execute(f"UPDATE entries SET {set_sql} WHERE id = ?",
                     (*updates.values(), entry_id))
        # Multi-video pins (Oct 27): keep entry_videos in sync with an
        # edited primary — a new /video/ URL takes position 0 (the rest
        # of the list stays as more-videos), an emptied field clears
        # the list, a non-video URL (live room) leaves the list alone.
        if "tiktok_url" in updates:
            tt_new = updates["tiktok_url"]
            if not tt_new or "/video/" in tt_new:
                set_entry_primary_video(conn, entry_id, tt_new)
        conn.commit()
    return JSONResponse({"ok": True, "id": entry_id, "updated": updates})


@app.post("/admin/media/{entry_id}")
async def admin_media(entry_id: int, request: Request, media: UploadFile = File(None)):
    """Attach/replace media for an entry (admin)."""
    _require_admin(request)
    if not media or not media.filename:
        return JSONResponse({"error": "No file"}, status_code=400)
    ext = safe_ext(media.filename)
    if ext not in PHOTO_EXTS:
        return JSONResponse({"error": "Photos only (JPG/PNG/WebP)"}, status_code=400)

    # Image decode + thumbnail and the update run in the thread pool,
    # never on the event loop (blip hardening, Oct 25) — original flow.
    def _store() -> JSONResponse:
        tmp = save_upload(media, MAX_PHOTO_BYTES)
        try:
            with Image.open(tmp) as im:
                im.verify()
        except (UnidentifiedImageError, OSError):
            tmp.unlink(missing_ok=True)
            return JSONResponse({"error": "Not a readable image"}, status_code=400)
        name = uuid.uuid4().hex
        media_rel = f"{name}{ext}"
        shutil.move(tmp, UPLOAD_DIR / media_rel)
        try:
            thumb_rel = make_thumb(UPLOAD_DIR / media_rel, name)
        except (OSError, UnidentifiedImageError):
            thumb_rel = media_rel
        with get_conn(DB_PATH) as conn:
            conn.execute("UPDATE entries SET media_path = ?, thumb_path = ?, media_type = 'photo' WHERE id = ?",
                         (media_rel, thumb_rel, entry_id))
            conn.commit()
        return JSONResponse({"ok": True, "id": entry_id})

    return await run_in_threadpool(_store)


# ---------------------------------------------------------------- sponsors

@app.get("/sponsor/click/{sponsor_id}")
def sponsor_click(sponsor_id: int):
    """Track a sponsor banner click, then redirect to the sponsor's website."""
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT id, website_url, is_active FROM sponsors WHERE id = ?",
            (sponsor_id,)).fetchone()
        if not row:
            raise HTTPException(404, "Sponsor not found")
        if row["is_active"]:
            conn.execute("UPDATE sponsors SET clicks = clicks + 1 WHERE id = ?", (sponsor_id,))
            conn.commit()
        url = (row["website_url"] or "").strip()
    if not url:
        raise HTTPException(404, "Sponsor has no website")
    if not url.startswith(("http://", "https://")):
        url = "https://" + url
    return RedirectResponse(url, status_code=302)


@app.get("/admin/sponsors", response_class=HTMLResponse)
def admin_sponsors(request: Request):
    if not is_admin(request):
        return RedirectResponse("/admin", status_code=303)
    with get_conn(DB_PATH) as conn:
        sponsors = [dict(r) for r in conn.execute(
            "SELECT * FROM sponsors ORDER BY is_active DESC, created_at DESC").fetchall()]
    return templates.TemplateResponse(request, "admin_sponsors.html",
        {"request": request, "sponsors": sponsors,
         "tier_labels": {"featured": "$250 Featured", "premium": "$500 Premium", "title": "$1,000 Title Sponsor"}})


@app.post("/admin/sponsors/add")
async def admin_sponsor_add(request: Request,
                            business_name: str = Form(""),
                            website_url: str = Form(""),
                            tier: str = Form("featured"),
                            banner_text: str = Form(""),
                            logo: UploadFile = File(None)):
    """Add a new sponsor (admin)."""
    _require_admin(request)
    business_name = business_name.strip()
    website_url = website_url.strip()
    if not business_name or not website_url:
        raise HTTPException(400, "Business name and website URL are required")
    if tier not in ("featured", "premium", "title"):
        tier = "featured"
    logo_path = None
    if logo and logo.filename:
        ext = safe_ext(logo.filename)
        if ext not in PHOTO_EXTS:
            raise HTTPException(400, "Logo must be JPG, PNG, or WebP")

        # Logo decode + orientation fix run in the thread pool, never on
        # the event loop (blip hardening, Oct 25) — original flow.
        def _process_logo() -> str:
            tmp = save_upload(logo, MAX_PHOTO_BYTES)
            try:
                with Image.open(tmp) as im:
                    im.verify()
            except (UnidentifiedImageError, OSError):
                tmp.unlink(missing_ok=True)
                raise HTTPException(400, "Not a readable image")
            sponsor_dir = UPLOAD_DIR / "sponsors"
            sponsor_dir.mkdir(exist_ok=True)
            path = f"sponsors/{uuid.uuid4().hex}{ext}"
            shutil.move(tmp, UPLOAD_DIR / path)
            _normalize_orientation(UPLOAD_DIR / path)
            return path

        logo_path = await run_in_threadpool(_process_logo)
    now = datetime.now(timezone.utc).isoformat()
    with get_conn(DB_PATH) as conn:
        conn.execute(
            "INSERT INTO sponsors (business_name, logo_path, website_url, tier, banner_text, is_active, clicks, created_at)"
            " VALUES (?, ?, ?, ?, ?, 1, 0, ?)",
            (business_name, logo_path, website_url, tier, banner_text.strip() or None, now))
        conn.commit()
    return RedirectResponse("/admin/sponsors", status_code=303)


@app.post("/admin/sponsors/{sponsor_id}/toggle")
def admin_sponsor_toggle(sponsor_id: int, request: Request):
    """Toggle a sponsor active/inactive (admin)."""
    _require_admin(request)
    with get_conn(DB_PATH) as conn:
        conn.execute("UPDATE sponsors SET is_active = 1 - is_active WHERE id = ?", (sponsor_id,))
        conn.commit()
    return RedirectResponse("/admin/sponsors", status_code=303)


@app.post("/admin/sponsors/{sponsor_id}/delete")
def admin_sponsor_delete(sponsor_id: int, request: Request):
    """Delete a sponsor and its logo (admin)."""
    _require_admin(request)
    with get_conn(DB_PATH) as conn:
        row = conn.execute("SELECT logo_path FROM sponsors WHERE id = ?", (sponsor_id,)).fetchone()
        conn.execute("DELETE FROM sponsors WHERE id = ?", (sponsor_id,))
        conn.commit()
    if row and row["logo_path"]:
        (UPLOAD_DIR / row["logo_path"]).unlink(missing_ok=True)
    return RedirectResponse("/admin/sponsors", status_code=303)



# =============================================================== HauntMap Social
# Phase 1, step 1 (STAGED — plan: files/hauntmap-social-plan-2026-10-24.md).
# Open member sign-ups + public profiles at /@handle. Browsing the map
# stays account-free; accounts are only for joining. Sessions are
# DATABASE-backed (table `sessions`, sha256 token hashes) — deliberately
# NOT the admin's in-memory pattern, which wipes on every deploy.
MEMBER_COOKIE = "hm_member"
MEMBER_SESSION_DAYS = 30
PBKDF2_ITERATIONS = 600_000
SOCIAL_AGE_MIN = 13  # plan §7 recommended default — staged ON, Dan to rule
CREATOR_HOLD_DAYS = 30  # plan §7 recommended default — staged ON

HANDLE_RE = re.compile(r"^[a-z0-9_]{3,20}$")
RESERVED_HANDLES = {
    "admin", "hauntmap", "support", "help", "official", "staff", "team",
    "moderator", "mod", "system", "root", "api", "login", "logout",
    "signup", "register", "settings", "profile", "edit", "about", "terms",
    "frank",
    "privacy", "events", "map", "watch", "tour", "tours", "nearby", "chat",
    "games", "music", "movies", "markets", "leaderboard", "passport",
    "daily", "towns", "advertise", "upload", "diy", "fanart", "fan-art",
    "jollymap", "gethauntmap", "haunt", "halloween", "christmas",
}

# Preset spooky avatars (step 1: no photo uploads). Key -> (emoji, tile bg).
AVATAR_PRESETS = {
    "pumpkin": ("🎃", "#3a1c66"),
    "ghost": ("👻", "#241243"),
    "skull": ("💀", "#1c1c26"),
    "bat": ("🦇", "#150826"),
    "witch": ("🧙", "#0d2818"),
    "vampire": ("🧛", "#2b0a12"),
    "spider": ("🕷️", "#101018"),
    "blackcat": ("🐈\u200d⬛", "#1a1030"),
    "owl": ("🦉", "#20140a"),
    "moon": ("🌙", "#0a1030"),
    "candy": ("🍬", "#30102a"),
    "zombie": ("🧟", "#12260d"),
}
# Preset profile banners (CSS gradients — curated, the MySpace flavor
# without raw CSS). Key -> gradient.
BANNER_PRESETS = {
    "midnight": "linear-gradient(120deg,#150826,#3a1c66 55%,#6d28a8)",
    "pumpkin": "linear-gradient(120deg,#2b1200,#8a3c00 55%,#ff7b1c)",
    "blood": "linear-gradient(120deg,#1c0208,#5c0a18 55%,#a1121f)",
    "slime": "linear-gradient(120deg,#0c2405,#2d5a12 55%,#6abe30)",
    "graveyard": "linear-gradient(120deg,#0d0d12,#26262e 55%,#4a4a55)",
    "candy": "linear-gradient(120deg,#2b0a24,#7a1c5e 55%,#ff5da2)",
}
DEFAULT_BANNER = "midnight"

# ------------------------------------------------------- HauntSocial Phase A
# Dan (Oct 25): the social network is named HauntSocial, and the
# MySpace-success lessons (research brief, 2026-10-25) land here:
# a mascot host (our "Tom"), the wall as currency (treats), one profile
# anthem, a Top 8 of THINGS (never people), and SAFE preset themes —
# customization via variables only, no member CSS/JS, ever.
# Phase B (bulletins, founding-creator seeding, member directory,
# Haunt of the Day, member data export) is a later build.

# Treat stickers a wall comment can carry — exactly ONE per comment.
TREAT_STICKERS = ["🎃", "👻", "🍬", "🦇", "🕷️", "💀"]

# Preset profile themes, applied as CSS-variable overrides on the
# member's own profile page only. "midnight" is the standing look.
PROFILE_THEMES = {
    "midnight": {"label": "Midnight", "vars": {}, "panel": ""},
    "pumpkin": {"label": "Pumpkin",
                "vars": {"--accent": "#ff7518", "--accent2": "#ffab5e",
                         "--card": "#2a1708", "--bg2": "#1c0f04"},
                "panel": "radial-gradient(120% 90% at 50% 0%, "
                         "rgba(255,117,24,.16), transparent 62%)"},
    "slime": {"label": "Slime",
              "vars": {"--accent": "#6abe30", "--accent2": "#a5e075",
                       "--card": "#12240c", "--bg2": "#0a1706"},
              "panel": "radial-gradient(120% 90% at 50% 0%, "
                       "rgba(106,190,48,.15), transparent 62%)"},
    "bloodmoon": {"label": "Blood Moon",
                  "vars": {"--accent": "#e0313c", "--accent2": "#ff8a7a",
                           "--card": "#2a0a10", "--bg2": "#190509"},
                  "panel": "radial-gradient(120% 90% at 50% 0%, "
                           "rgba(224,49,60,.16), transparent 62%)"},
    "graveyard": {"label": "Graveyard",
                  "vars": {"--accent": "#9a8cff", "--accent2": "#c9c2ff",
                           "--card": "#1e1e28", "--bg2": "#12121a"},
                  "panel": "radial-gradient(120% 90% at 50% 0%, "
                           "rgba(154,140,255,.14), transparent 62%)"},
}
DEFAULT_THEME = "midnight"

# "Get to know me" bundle (Dan, Oct 25): optional profile fields that
# give members something to talk about. Picks store keys; labels and
# emoji live here so the edit pickers and the profile badges can never
# drift apart. Scare tolerance reuses the Scare-O-Meter's own scale
# (SCARE_LEVELS + the labels/emoji the detail-page widget shows).
GTK_SCARE_META = {
    "family": ("😊", "Family-friendly"),
    "spooky": ("👻", "Spooky"),
    "creepy": ("🧛", "Creepy"),
    "terrifying": ("😱", "Terrifying"),
    "extreme": ("💀", "Extreme"),
}
GTK_COSTUME_PICKS = {
    "yes": "Dressing up",
    "no": "Sitting out",
    "undecided": "Undecided",
}
GTK_HAUNTER_KINDS = {
    "decorator": ("🎃", "Decorator"),
    "scare_actor": ("👹", "Scare actor"),
    "haunt_chaser": ("🗺️", "Haunt chaser"),
    "party_host": ("🥳", "Party host"),
    "candy_pro": ("🍬", "Candy pro"),
}
GTK_MONSTERS = {
    "vampire": ("🧛", "Vampire"),
    "ghost": ("👻", "Ghost"),
    "werewolf": ("🐺", "Werewolf"),
    "witch": ("🧙", "Witch"),
    "zombie": ("🧟", "Zombie"),
    "skeleton": ("💀", "Skeleton"),
    "demon": ("😈", "Demon"),
}
GTK_SEASON_PICKS = {
    "sep1": "September 1",
    "oct1": "October 1",
    "yearround": "Year-round 🎃",
}
# Char caps for the bundle's free-text fields (form key == column).
GTK_TEXT_CAPS = {
    "fav_joke": 140, "costume_as": 80, "best_memory": 500,
    "candy_fav": 60, "candy_trade": 60, "first_horror": 120,
    "haunt_name": 80, "haunt_theme": 80, "fav_song": 120,
}
GTK_PICK_KEYS = {
    "costume_pick": GTK_COSTUME_PICKS,
    "scare_tolerance": GTK_SCARE_META,
    "haunter_kind": GTK_HAUNTER_KINDS,
    "monster_ego": GTK_MONSTERS,
    "season_start": GTK_SEASON_PICKS,
}
GTK_COLUMNS = tuple(GTK_TEXT_CAPS) + tuple(GTK_PICK_KEYS)


def _gtk_view(profile: dict, has_anthem: bool,
              primary_haunt_id: int | None) -> dict | None:
    """"Get to know me" as profile.html renders it, or None when the
    member has set nothing (the section then doesn't render at all, so
    an unset profile is byte-identical to before the bundle)."""
    g = profile.get
    badges = []
    if g("haunter_kind") in GTK_HAUNTER_KINDS:
        emoji, label = GTK_HAUNTER_KINDS[g("haunter_kind")]
        badges.append(f"{emoji} {label}")
    if g("monster_ego") in GTK_MONSTERS:
        emoji, label = GTK_MONSTERS[g("monster_ego")]
        badges.append(f"{emoji} {label}")
    if g("scare_tolerance") in GTK_SCARE_META:
        emoji, label = GTK_SCARE_META[g("scare_tolerance")]
        badges.append(f"Scare tolerance: {emoji} {label}")
    costume_line = None
    if g("costume_pick") == "yes":
        costume_line = "🎭 Dressing up"
        if g("costume_as"):
            costume_line += f" as {g('costume_as')}"
        costume_line += " this year"
    elif g("costume_pick") == "no":
        costume_line = "🎭 Sitting out the costume this year"
    elif g("costume_pick") == "undecided":
        costume_line = "🎭 Costume this year: still deciding"
    candy_line = None
    if g("candy_fav") or g("candy_trade"):
        parts = []
        if g("candy_fav"):
            parts.append(f"Loves {g('candy_fav')}")
        if g("candy_trade"):
            parts.append(f"Trades away {g('candy_trade')}")
        candy_line = "🍬 " + " · ".join(parts)
    rows = []
    if g("fav_joke"):
        rows.append(("Favorite Halloween joke", g("fav_joke"), None))
    if g("first_horror"):
        rows.append(("First horror movie I ever saw",
                     g("first_horror"), None))
    if g("haunt_name"):
        haunt_text = g("haunt_name")
        if g("haunt_theme"):
            haunt_text += f" — {g('haunt_theme')}"
        rows.append(("My haunt this year", haunt_text,
                     f"/d/{primary_haunt_id}" if primary_haunt_id else None))
    if g("season_start") in GTK_SEASON_PICKS:
        rows.append(("Spooky season starts",
                     GTK_SEASON_PICKS[g("season_start")], None))
    if g("fav_song") and not has_anthem:
        # With an anthem the song captions the player instead (profile.html).
        rows.append(("Favorite Halloween song", g("fav_song"), None))
    memory = g("best_memory") or None
    if not (badges or costume_line or candy_line or rows or memory):
        return None
    return {"badges": badges, "costume_line": costume_line,
            "candy_line": candy_line, "rows": rows, "memory": memory}


# Frank — the official HauntSocial host (the MySpace "Tom" lesson:
# nobody lands in an empty room). A normal member row flagged
# is_official; no admin powers, no special routes.
FRANK_HANDLE = "frank"
FRANK_EMAIL = "frank@gethauntmap.com"
FRANK_ART = "/static/img/frank_host_art.webp"  # Dan's new header Frank (full art, banner)
FRANK_AVATAR_ART = "/static/img/frank_avatar.webp"  # head/face crop of the same art
FRANK_AVATAR_CHOICE = "frank_art"
FRANK_BANNER_CHOICE = "frank_art"
FRANK_BIO = ("Your HauntSocial host — I haunt every profile so nobody's "
             "wall is ever empty. Leave treats, show me your haunt, and "
             "make yourself at home. 🎃")
# "Monster Mash" — Bobby "Boris" Pickett (official lyric video,
# Radial by The Orchard). The ID was oEmbed-verified for the /music
# page on 2026-10-23; the anthem slot's validator accepts it.
FRANK_ANTHEM_URL = "https://www.youtube.com/watch?v=NF69rFld9zQ"
FRANK_WELCOME = ("Welcome to HauntSocial 🎃 I'm Frank, your host — I follow "
                 "every new haunter so this place never feels empty. Set "
                 "your anthem, pick your Top 8, and leave a treat on my "
                 "wall anytime. Happy haunting!")

# @gethauntmap — the official brand account (Plan B, Dan Oct 25): a
# separate, login-able account alongside Dan's personal @dan. Created
# by the app exactly like Frank, except its password comes from the
# HAUNTSOCIAL_BRAND_PASSWORD env var (Dan sets it in Render), because
# no self-serve change-password exists anywhere in the app — see
# _ensure_gethauntmap. The handle is in RESERVED_HANDLES, so no member
# can ever hold it.
BRAND_HANDLE = "gethauntmap"
BRAND_EMAIL = "gethauntmap+social@gmail.com"  # Dan's pick (plus-address)
BRAND_BIO = ("The official HauntMap account — the Halloween map that "
             "builds your fright night for you. New haunts daily. 🎃")
BRAND_AVATAR_CHOICE = "ghost"     # AVATAR_PRESETS key (👻) — the brand mark
BRAND_BANNER_CHOICE = "midnight"  # BANNER_PRESETS key; matches the theme


def _theme_view(theme_key: str | None) -> dict:
    """Inline style + class for a profile article under a preset theme.
    Midnight returns empty strings so today's look stays pixel-exact."""
    key = theme_key if theme_key in PROFILE_THEMES else DEFAULT_THEME
    theme = PROFILE_THEMES[key]
    if key == DEFAULT_THEME:
        return {"key": key, "style": "", "class": ""}
    decls = "; ".join(f"{k}: {v}" for k, v in theme["vars"].items())
    if theme["panel"]:
        decls += f"; background: {theme['panel']}"
    return {"key": key, "style": decls, "class": " soc-themed"}


def _ensure_frank(conn) -> int | None:
    """Frank's user id, creating him on first need. Returns None when
    the handle is held by a non-official account — never hijack it."""
    row = conn.execute("SELECT id, is_official FROM users WHERE handle = ?",
                       (FRANK_HANDLE,)).fetchone()
    if row:
        return row["id"] if row["is_official"] else None
    if conn.execute("SELECT 1 FROM users WHERE email = ?",
                    (FRANK_EMAIL,)).fetchone():
        return None
    pw_hash, pw_salt = _hash_password(secrets.token_urlsafe(32))
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO users (email, password_hash, password_salt, handle, "
        "is_official, created_at) VALUES (?, ?, ?, ?, 1, ?)",
        (FRANK_EMAIL, pw_hash, pw_salt, FRANK_HANDLE, now))
    frank_id = cur.lastrowid
    conn.execute(
        "INSERT INTO profiles (user_id, display_name, bio, town, "
        "avatar_choice, banner_choice, theme, music_embed_url, updated_at) "
        "VALUES (?, 'Frank', ?, 'HauntSocial HQ', ?, ?, 'graveyard', ?, ?)",
        (frank_id, FRANK_BIO, FRANK_AVATAR_CHOICE, FRANK_BANNER_CHOICE,
         FRANK_ANTHEM_URL, now))
    return frank_id


def _ensure_gethauntmap(conn) -> int | None:
    """The official @gethauntmap brand account's user id, creating it
    on first need. Mirrors _ensure_frank, with one difference: this
    account must be log-in-able, and there is NO self-serve
    change-password anywhere in the app — so while the
    HAUNTSOCIAL_BRAND_PASSWORD env var is set, it IS this account's
    password: the stored hash is synced to it on every boot. Var absent
    at creation -> random token (Frank-style); login then stays
    deferred until Dan sets the var and the service restarts.
    Returns None when the handle is held by a non-official account or
    the email by a different account — never hijack either (same guard
    as Frank). No welcome treat, no follow inserts: the boot backfill
    in _hauntsocial_boot makes this account follow Frank like everyone
    else, and Frank stays the only auto-follow for new signups."""
    row = conn.execute("SELECT id, is_official FROM users WHERE handle = ?",
                       (BRAND_HANDLE,)).fetchone()
    if row and not row["is_official"]:
        return None
    if row:
        brand_id = row["id"]
        brand_pw = os.environ.get("HAUNTSOCIAL_BRAND_PASSWORD")
        if brand_pw:
            acct = conn.execute(
                "SELECT password_hash, password_salt FROM users "
                "WHERE id = ?", (brand_id,)).fetchone()
            if acct and not _check_password(
                    brand_pw, acct["password_hash"], acct["password_salt"]):
                pw_hash, pw_salt = _hash_password(brand_pw)
                conn.execute(
                    "UPDATE users SET password_hash = ?, "
                    "password_salt = ? WHERE id = ?",
                    (pw_hash, pw_salt, brand_id))
        return brand_id
    if conn.execute("SELECT 1 FROM users WHERE email = ?",
                    (BRAND_EMAIL,)).fetchone():
        return None
    brand_pw = os.environ.get("HAUNTSOCIAL_BRAND_PASSWORD") or \
        secrets.token_urlsafe(32)
    pw_hash, pw_salt = _hash_password(brand_pw)
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.execute(
        "INSERT INTO users (email, password_hash, password_salt, handle, "
        "is_official, created_at) VALUES (?, ?, ?, ?, 1, ?)",
        (BRAND_EMAIL, pw_hash, pw_salt, BRAND_HANDLE, now))
    brand_id = cur.lastrowid
    conn.execute(
        "INSERT INTO profiles (user_id, display_name, bio, town, "
        "avatar_choice, banner_choice, theme, updated_at) "
        "VALUES (?, 'HauntMap', ?, 'HauntSocial HQ', ?, ?, 'midnight', ?)",
        (brand_id, BRAND_BIO, BRAND_AVATAR_CHOICE, BRAND_BANNER_CHOICE,
         now))
    return brand_id


def _frank_follow_and_welcome(conn, new_user_id: int) -> None:
    """New-signup mechanics: the member auto-follows Frank, and Frank
    leaves the welcome treat on THEIR wall (their first wall comment)."""
    frank_id = _ensure_frank(conn)
    if not frank_id or frank_id == new_user_id:
        return
    now = datetime.now(timezone.utc).isoformat()
    conn.execute(
        "INSERT OR IGNORE INTO follows (follower_id, followee_id, "
        "created_at) VALUES (?, ?, ?)", (new_user_id, frank_id, now))
    conn.execute(
        "INSERT INTO wall_comments (profile_user_id, author_user_id, "
        "text, sticker, created_at) VALUES (?, ?, ?, ?, ?)",
        (new_user_id, frank_id, FRANK_WELCOME, "🎃", now))


# One-time coordinate corrections (Dan approved Oct 26, 2026; from the
# 2026-10-26 address cleanup — hidden_files/address-cleanup-2026-10-26/
# CHANGELOG.md): these pins' stored coords plot in the wrong town while
# their verified street addresses are correct, and /admin/edit cannot
# write lat/lng, so the fix ships as a guarded boot-time data patch.
# Every target was re-verified against a fresh forward geocode of the
# pin's own address (house/street-number match in the stated town)
# before shipping. Two more pins from the cleanup's flag list (4876,
# 4733) were checked and deliberately EXCLUDED: their stored dots
# proved correct (venue/source coords + address ZIP agree) — the
# cleanup's geocoder had matched a same-named street across town.
PIN_COORD_FIXES: dict[int, tuple[float, float]] = {
    1998: (33.7327901, -84.373733),    # 800 Cherokee Ave SE, Atlanta, GA (dot was in Louisville, KY)
    3873: (36.1805135, -86.2997785),   # 7040 Murfreesboro Road, Lebanon, TN 37090
    5137: (41.5637236, -88.2993717),   # 3305 Caton Farm Rd, Joliet, IL 60431
    5140: (39.5660658, -105.0355237),  # 7877 Elmwood St, Littleton, CO (Wolhurst segment)
    5405: (39.610876, -75.6587366),    # 3570 Red Lion Rd, Bear, DE 19701
    4649: (38.8524501, -104.7968836),  # 7102 Palmer Park Blvd, Colorado Springs, CO 80909
    5582: (45.4193154, -122.4626114),  # 11740 SE Sunnyside Rd, Damascus, OR 97015
    4276: (27.832393, -82.7593773),    # 12190 66th Ave N, Seminole, FL 33772
    4737: (47.6855673, -122.1012804),  # 13817 180th Ave NE, Redmond, WA 98052
    336: (40.6814933, -73.3689508),    # 417 South 1st Street, Lindenhurst, NY
    5538: (36.111158, -86.7476142),    # 502 Thompson Ln, Nashville, TN 37211
    3787: (34.1483499, -118.0014517),  # 223 W El Sur St, Monrovia, CA 91016
    98: (40.7616522, -73.3902444),     # 185 Colonial Springs Rd, Wheatley Heights, NY
    5766: (40.0696478, -74.0797665),   # 1507 River Ave, Point Pleasant, NJ 08742
}


def _apply_pin_coord_fixes() -> None:
    """Move the misplaced map dots in PIN_COORD_FIXES onto their pins'
    verified addresses. Guarded + idempotent: a row is only rewritten
    while its stored point is still >0.3 mi from the verified point, so
    reboots are no-ops and a future legitimate re-geocode that lands on
    the address is never fought."""
    applied = 0
    with get_conn(DB_PATH) as conn:
        for pid, (lat, lng) in PIN_COORD_FIXES.items():
            row = conn.execute(
                "SELECT lat, lng FROM entries WHERE id = ?", (pid,)).fetchone()
            if not row or row["lat"] is None or row["lng"] is None:
                continue
            if haversine_miles(row["lat"], row["lng"], lat, lng) > 0.3:
                conn.execute(
                    "UPDATE entries SET lat = ?, lng = ? WHERE id = ?",
                    (lat, lng, pid))
                applied += 1
        conn.commit()
    if applied:
        logger.info("Pin coord fixes applied to %d entries", applied)


def _hauntsocial_boot() -> None:
    """Startup: Frank exists, and every existing member follows him —
    the backfill for members who joined before he did. Follows only:
    no wall spam for existing members."""
    with get_conn(DB_PATH) as conn:
        frank_id = _ensure_frank(conn)
        _ensure_gethauntmap(conn)
        if frank_id:
            now = datetime.now(timezone.utc).isoformat()
            conn.execute(
                "INSERT OR IGNORE INTO follows (follower_id, followee_id, "
                "created_at) SELECT id, ?, ? FROM users WHERE id != ?",
                (frank_id, now, frank_id))
        conn.commit()


def _film_catalog_titles() -> list[str]:
    """Every film title in the site's /movies catalog (deduped) — the
    Top 8 film picker offers these first; free text is also allowed."""
    titles, seen = [], set()
    for lst in (MOVIE_NEW, MOVIE_CLASSICS, MOVIE_DEEP_CUTS, MOVIE_FREE_FULL):
        for m in lst:
            t = (m.get("title") or "").strip()
            if t and t.lower() not in seen:
                seen.add(t.lower())
                titles.append(t)
    return sorted(titles, key=str.lower)


# Simple in-app throttle for auth endpoints: key -> [unix timestamps].
_auth_throttle: dict[str, list[float]] = {}


def _throttle_hit(key: str, limit: int, window_s: int) -> bool:
    """Record one attempt; True when the caller is OVER the limit."""
    now = time.time()
    hits = [t for t in _auth_throttle.get(key, []) if now - t < window_s]
    hits.append(now)
    _auth_throttle[key] = hits
    return len(hits) > limit


def _client_ip(request: Request) -> str:
    fwd = request.headers.get("x-forwarded-for", "")
    if fwd:
        return fwd.split(",")[0].strip()
    return request.client.host if request.client else "unknown"


def _hash_password(password: str, salt_hex: str | None = None) -> tuple[str, str]:
    salt = bytes.fromhex(salt_hex) if salt_hex else secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), salt, PBKDF2_ITERATIONS)
    return digest.hex(), salt.hex()


def _check_password(password: str, hash_hex: str, salt_hex: str) -> bool:
    digest, _ = _hash_password(password, salt_hex)
    return hmac.compare_digest(digest, hash_hex)


def _start_member_session(response: Response, user_id: int) -> None:
    token = secrets.token_urlsafe(32)
    token_hash = hashlib.sha256(token.encode()).hexdigest()
    now = datetime.now(timezone.utc)
    with get_conn(DB_PATH) as conn:
        conn.execute(
            "INSERT INTO sessions (token_hash, user_id, created_at, expires_at) "
            "VALUES (?, ?, ?, ?)",
            (token_hash, user_id, now.isoformat(),
             (now + timedelta(days=MEMBER_SESSION_DAYS)).isoformat()))
        conn.commit()
    response.set_cookie(MEMBER_COOKIE, token, max_age=MEMBER_SESSION_DAYS * 24 * 3600,
                        httponly=True, samesite="lax")


def current_member(request: Request) -> dict | None:
    """The logged-in member for this request, or None. Suspended accounts
    read as logged out."""
    token = request.cookies.get(MEMBER_COOKIE)
    if not token:
        return None
    token_hash = hashlib.sha256(token.encode()).hexdigest()
    now = datetime.now(timezone.utc).isoformat()
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT u.* FROM sessions s JOIN users u ON u.id = s.user_id "
            "WHERE s.token_hash = ? AND s.expires_at > ?",
            (token_hash, now)).fetchone()
    if row is None or row["status"] != "active":
        return None
    return dict(row)


def _social_meta_get(key: str) -> str | None:
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT value FROM social_meta WHERE key = ?", (key,)).fetchone()
    return row["value"] if row else None


def _social_meta_set(key: str, value: str) -> None:
    with get_conn(DB_PATH) as conn:
        conn.execute(
            "INSERT INTO social_meta (key, value) VALUES (?, ?) "
            "ON CONFLICT(key) DO UPDATE SET value = excluded.value",
            (key, value))
        conn.commit()


def _creator_hold_until() -> datetime:
    """Creator-handle holds run CREATOR_HOLD_DAYS from the first time the
    social schema wakes up (i.e. launch); the date is pinned in
    social_meta on first use so deploys don't extend it."""
    raw = _social_meta_get("creator_hold_until")
    if raw:
        try:
            return datetime.fromisoformat(raw)
        except ValueError:
            pass
    until = datetime.now(timezone.utc) + timedelta(days=CREATOR_HOLD_DAYS)
    _social_meta_set("creator_hold_until", until.isoformat())
    return until


def _normalize_handle_candidate(name: str) -> str:
    """Turn a credited creator display_name into its handle-shaped form:
    'lilroamingexplorers (TikTok)' -> 'lilroamingexplorers',
    '@laurschor on TikTok' -> 'laurschor', 'Ro Roaming (TikTok)' ->
    'roroaming'."""
    s = (name or "").strip().lower()
    s = re.sub(r"\s*\(tiktok\)\s*$", "", s)
    s = re.sub(r"\s+on tiktok\s*$", "", s)
    s = s.lstrip("@").strip()
    s = re.sub(r"[^a-z0-9_]", "", s)
    return s


_creator_holds_cache: tuple[float, set[str]] = (0.0, set())


def _creator_hold_handles() -> set[str]:
    """Handles matching creators already credited on the map (from the
    entries table's display_name values), cached for an hour."""
    global _creator_holds_cache
    ts, cached = _creator_holds_cache
    if time.time() - ts < 3600 and cached:
        return cached
    holds: set[str] = set()
    try:
        with get_conn(DB_PATH) as conn:
            rows = conn.execute(
                "SELECT DISTINCT display_name FROM entries "
                "WHERE display_name IS NOT NULL AND display_name != ''").fetchall()
        for r in rows:
            cand = _normalize_handle_candidate(r["display_name"])
            if HANDLE_RE.match(cand) and cand not in RESERVED_HANDLES:
                holds.add(cand)
    except Exception:
        pass  # holds are a courtesy layer; never break signup over them
    _creator_holds_cache = (time.time(), holds)
    return holds


def _handle_held(handle: str) -> bool:
    if datetime.now(timezone.utc) >= _creator_hold_until():
        return False
    return handle in _creator_hold_handles()


def _avatar_view(choice: str | None, display_name: str | None, handle: str,
                 avatar_path: str | None = None) -> dict:
    if avatar_path:
        # An uploaded profile picture beats every preset (Dan, Oct 25).
        # Frank never has one — his row carries only the art choice below.
        return {"emoji": "", "bg": "#241243", "initial": "",
                "img": f"/media/{avatar_path}"}
    if choice == FRANK_AVATAR_CHOICE:
        # The host's avatar is the head/face crop of Dan's new Frank art.
        return {"emoji": "", "bg": "#12260d", "initial": "", "img": FRANK_AVATAR_ART}
    if choice in AVATAR_PRESETS:
        emoji, bg = AVATAR_PRESETS[choice]
        return {"emoji": emoji, "bg": bg, "initial": ""}
    initial = (display_name or handle or "?").strip()[:1].upper() or "?"
    return {"emoji": "", "bg": "#3a1c66", "initial": initial}


def _music_embed(url: str | None) -> dict | None:
    """Convert a member's Spotify / SoundCloud / YouTube URL into an embed.
    Embeds ONLY — the platforms hold the files and the licenses (plan §2
    Phase 3). Returns None for anything unrecognized or off-host."""
    if not url:
        return None
    try:
        u = urllib.parse.urlparse(url.strip())
    except ValueError:
        return None
    host = (u.hostname or "").lower()
    if host == "open.spotify.com":
        m = re.match(r"^/(track|album|playlist|episode|show)/([A-Za-z0-9]+)", u.path)
        if m:
            kind, sid = m.group(1), m.group(2)
            return {"kind": "spotify",
                    "src": f"https://open.spotify.com/embed/{kind}/{sid}",
                    "height": 152 if kind in ("track", "episode") else 352}
        return None
    if host in ("www.youtube.com", "youtube.com", "m.youtube.com"):
        vid = urllib.parse.parse_qs(u.query).get("v", [None])[0]
        if not vid:
            m = re.match(r"^/(?:shorts|embed)/([\w-]{6,})", u.path)
            vid = m.group(1) if m else None
        if vid and re.fullmatch(r"[\w-]{6,}", vid):
            return {"kind": "youtube",
                    "src": f"https://www.youtube.com/embed/{vid}", "height": 315}
        return None
    if host == "youtu.be":
        vid = u.path.strip("/").split("/")[0]
        if re.fullmatch(r"[\w-]{6,}", vid or ""):
            return {"kind": "youtube",
                    "src": f"https://www.youtube.com/embed/{vid}", "height": 315}
        return None
    if host in ("soundcloud.com", "www.soundcloud.com"):
        if u.path and u.path != "/":
            src = ("https://w.soundcloud.com/player/?url="
                   + urllib.parse.quote(url.strip(), safe="")
                   + "&color=%23ff6a00&auto_play=false&hide_related=true"
                     "&show_comments=false&show_user=true")
            return {"kind": "soundcloud", "src": src, "height": 166}
        return None
    return None


def _contains_link(text: str) -> bool:
    return bool(re.search(r"https?://|www\.", text or "", re.IGNORECASE))


def _account_age_days(user: dict) -> int:
    try:
        created = datetime.fromisoformat(str(user["created_at"]).replace("Z", "+00:00"))
        if created.tzinfo is None:
            created = created.replace(tzinfo=timezone.utc)
        return (datetime.now(timezone.utc) - created).days
    except (ValueError, KeyError):
        return 9999


def _member_since_label(created_at: str | None) -> str:
    try:
        d = datetime.fromisoformat(str(created_at).replace("Z", "+00:00"))
        return d.strftime("%B %Y")
    except (ValueError, TypeError):
        return ""


def _safe_next(next_url: str | None) -> str | None:
    if next_url and next_url.startswith("/") and not next_url.startswith("//"):
        return next_url
    return None


# ---------------------------------------------------------------- signup/login

@app.get("/signup", response_class=HTMLResponse)
def signup_form(request: Request):
    member = current_member(request)
    if member:
        return RedirectResponse(f"/@{member['handle']}", status_code=303)
    return templates.TemplateResponse(request, "signup.html",
                                      {"request": request, "error": None,
                                       "values": {}})


@app.post("/signup", response_class=HTMLResponse)
def signup_submit(request: Request,
                  email: str = Form(""), handle: str = Form(""),
                  password: str = Form(""), dob: str = Form(""),
                  agree_terms: str = Form("")):
    ip = _client_ip(request)
    values = {"email": email.strip(), "handle": handle.strip().lower(), "dob": dob}

    def fail(msg: str, status: int = 400):
        return templates.TemplateResponse(
            request, "signup.html",
            {"request": request, "error": msg, "values": values},
            status_code=status)

    if _throttle_hit(f"signup:{ip}", 5, 3600):
        return fail("Too many sign-ups from this connection — try again in a bit.", 429)
    email_n = email.strip().lower()
    handle_n = handle.strip().lower()
    if not re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email_n):
        return fail("That email doesn't look right — check it and try again.")
    if not HANDLE_RE.match(handle_n):
        return fail("Handles are 3–20 characters: lowercase letters, numbers, "
                    "and underscores only.")
    if handle_n in RESERVED_HANDLES:
        return fail("That name is reserved — pick another handle.")
    if len(password) < 8:
        return fail("Passwords need at least 8 characters.")
    if agree_terms not in ("yes", "on", "true"):
        return fail("Please agree to the Terms and Privacy Policy to join.")
    try:
        dob_d = datetime.strptime(dob, "%Y-%m-%d").date()
    except ValueError:
        return fail("Enter your date of birth — we use it only for the age check.")
    today = datetime.now(timezone.utc).date()
    age = today.year - dob_d.year - ((today.month, today.day) < (dob_d.month, dob_d.day))
    if age < SOCIAL_AGE_MIN:
        return fail("Sorry — you need to be 13 or older to join HauntSocial.")
    if age > 120:
        return fail("That date of birth doesn't look right — check it and try again.")
    with get_conn(DB_PATH) as conn:
        if conn.execute("SELECT 1 FROM users WHERE email = ?", (email_n,)).fetchone():
            return fail("That email already has an account — try signing in.")
        if conn.execute("SELECT 1 FROM users WHERE handle = ?", (handle_n,)).fetchone():
            return fail("That handle is taken — pick another.")
    if _handle_held(handle_n):
        return fail(
            "That name is reserved for its haunter — it's the name of a "
            "creator already credited on the map, held for them to claim. "
            "If that's you, hang tight: claiming opens soon, and we'll "
            "verify it's really you. Pick a different handle for now, or "
            "check back when claims open.")
    pw_hash, pw_salt = _hash_password(password)
    now = datetime.now(timezone.utc).isoformat()
    with get_conn(DB_PATH) as conn:
        cur = conn.execute(
            "INSERT INTO users (email, password_hash, password_salt, handle, "
            "dob, created_at) VALUES (?, ?, ?, ?, ?, ?)",
            (email_n, pw_hash, pw_salt, handle_n, dob, now))
        user_id = cur.lastrowid
        conn.execute(
            "INSERT INTO profiles (user_id, display_name, updated_at) "
            "VALUES (?, ?, ?)", (user_id, handle_n, now))
        # HauntSocial: auto-follow the host + his welcome treat lands on
        # the new member's wall in the same transaction.
        _frank_follow_and_welcome(conn, user_id)
        conn.commit()
    resp = RedirectResponse(f"/@{handle_n}", status_code=303)
    _start_member_session(resp, user_id)
    return resp


@app.get("/login", response_class=HTMLResponse)
def login_form(request: Request, next: str = ""):
    member = current_member(request)
    if member:
        return RedirectResponse(_safe_next(next) or f"/@{member['handle']}",
                                status_code=303)
    return templates.TemplateResponse(request, "login.html",
                                      {"request": request, "error": None,
                                       "next": _safe_next(next) or "", "email": ""})


@app.post("/login", response_class=HTMLResponse)
def login_submit(request: Request, email: str = Form(""),
                 password: str = Form(""), next: str = Form("")):
    ip = _client_ip(request)
    if _throttle_hit(f"login:{ip}", 10, 900):
        return templates.TemplateResponse(
            request, "login.html",
            {"request": request, "next": _safe_next(next) or "", "email": email,
             "error": "Too many tries — wait a few minutes and try again."},
            status_code=429)
    email_n = email.strip().lower()
    with get_conn(DB_PATH) as conn:
        row = conn.execute("SELECT * FROM users WHERE email = ?",
                           (email_n,)).fetchone()
    ok = row is not None and row["status"] == "active" and _check_password(
        password, row["password_hash"], row["password_salt"])
    if not ok:
        return templates.TemplateResponse(
            request, "login.html",
            {"request": request, "next": _safe_next(next) or "", "email": email,
             "error": "Email or password doesn't match — try again."},
            status_code=401)
    resp = RedirectResponse(_safe_next(next) or f"/@{row['handle']}", status_code=303)
    _start_member_session(resp, row["id"])
    return resp


@app.get("/logout")
@app.post("/logout")
def logout(request: Request):
    token = request.cookies.get(MEMBER_COOKIE)
    if token:
        token_hash = hashlib.sha256(token.encode()).hexdigest()
        with get_conn(DB_PATH) as conn:
            conn.execute("DELETE FROM sessions WHERE token_hash = ?", (token_hash,))
            conn.commit()
    resp = RedirectResponse("/", status_code=303)
    resp.delete_cookie(MEMBER_COOKIE)
    return resp


# ------------------------------------------- password reset (admin-queue path)
# There is NO email-sending code on the site yet. Until Dan creates the
# gethauntmap Gmail app password (plan §3), reset requests land in the
# password_reset_requests table — the admin queue — and get handled by
# hand. Nothing here pretends to send an email.

@app.get("/forgot-password", response_class=HTMLResponse)
def forgot_form(request: Request):
    return templates.TemplateResponse(request, "forgot_password.html",
                                      {"request": request, "sent": False})


@app.post("/forgot-password", response_class=HTMLResponse)
def forgot_submit(request: Request, email: str = Form("")):
    email_n = email.strip().lower()
    if re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", email_n or ""):
        with get_conn(DB_PATH) as conn:
            conn.execute(
                "INSERT INTO password_reset_requests (email, created_at) "
                "VALUES (?, ?)", (email_n, datetime.now(timezone.utc).isoformat()))
            conn.commit()
    # Same message either way — never leak whether an account exists.
    return templates.TemplateResponse(request, "forgot_password.html",
                                      {"request": request, "sent": True})


# ------------------------------------------------------------- legal (drafts)

@app.get("/terms", response_class=HTMLResponse)
def terms_page(request: Request):
    return templates.TemplateResponse(request, "terms.html", {"request": request})


@app.get("/privacy", response_class=HTMLResponse)
def privacy_page(request: Request):
    return templates.TemplateResponse(request, "privacy.html", {"request": request})


# ------------------------------------------------------- hauntsocial explainer

# --------------------------------------------------- PWA + Web Push
# Haunt Chat Wave 1 (Dan, Oct 27, 2026 — benchmark brief §4 headline
# #1): HauntMap as an installable PWA, plus opt-in web push so the
# chat room can call members back (@mentions, game challenges,
# replies, Frank announcements). The manifest + service worker are
# served from ROOT paths: a service worker's scope is its own path,
# so /sw.js must live at the root to cover the site. The SW is
# deliberately conservative — network-first for pages, runtime
# cache only for static assets — so it can never serve a stale
# site. Push plumbing lives in app/push.py; keys come from env.

@app.get("/manifest.webmanifest")
def pwa_manifest():
    return FileResponse(
        BASE_DIR / "static" / "manifest.webmanifest",
        media_type="application/manifest+json",
        headers={"Cache-Control": "public, max-age=3600"})


@app.get("/sw.js")
def pwa_service_worker():
    return FileResponse(
        BASE_DIR / "static" / "js" / "sw.js",
        media_type="application/javascript",
        headers={"Service-Worker-Allowed": "/",
                 "Cache-Control": "no-cache"})


@app.get("/api/push/config")
def push_config(request: Request):
    return {"configured": push_mod.configured(),
            "public_key": push_mod.public_key()}


@app.get("/api/push/settings")
def push_settings_get(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    with get_conn(DB_PATH) as conn:
        settings = push_mod.get_settings(conn, member["id"])
        count = push_mod.subscription_count(conn, member["id"])
    return {"settings": settings, "subscriptions": count,
            "configured": push_mod.configured()}


@app.post("/api/push/settings")
async def push_settings_save(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    try:
        data = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    with get_conn(DB_PATH) as conn:
        current = push_mod.get_settings(conn, member["id"])
        for key in push_mod.KINDS + ("enabled",):
            if key in data:
                current[key] = 1 if data[key] else 0
        saved = push_mod.save_settings(conn, member["id"], current)
        conn.commit()
    return {"ok": True, "settings": saved}


@app.post("/api/push/subscribe")
async def push_subscribe(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    try:
        data = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    endpoint = str(data.get("endpoint") or "")
    keys = data.get("keys") or {}
    p256dh = str(keys.get("p256dh") or "")
    auth = str(keys.get("auth") or "")
    # Real push services only ever issue https endpoints; loopback
    # http is allowed so a local rig can stand in for one.
    if not (endpoint.startswith("https://")
            or endpoint.startswith(("http://127.0.0.1",
                                      "http://localhost"))) \
            or not p256dh or not auth:
        return JSONResponse(
            {"ok": False, "error": "That subscription looks "
                                  "incomplete."}, status_code=400)
    with get_conn(DB_PATH) as conn:
        push_mod.store_subscription(
            conn, member["id"], endpoint, p256dh, auth,
            request.headers.get("user-agent", ""))
        conn.commit()
        count = push_mod.subscription_count(conn, member["id"])
    return {"ok": True, "subscriptions": count}


@app.post("/api/push/unsubscribe")
async def push_unsubscribe(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    try:
        data = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    endpoint = str(data.get("endpoint") or "")
    if endpoint:
        with get_conn(DB_PATH) as conn:
            push_mod.remove_subscription(conn, member["id"], endpoint)
            conn.commit()
    return {"ok": True}


@app.post("/api/push/test")
def push_test(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    if not push_mod.configured():
        return JSONResponse(
            {"ok": False, "error": "Notifications aren't switched "
                                   "on for the site yet."},
            status_code=503)
    push_mod.notify_user(
        DB_PATH, member["id"], "test",
        "🎃 HauntMap notifications are on!",
        "This is your test — mentions, challenges and Frank's "
        "announcements will find you here.", url="/chat",
        ref="test", online_ids=frozenset(), force=True)
    return {"ok": True}


@app.get("/hauntsocial", response_class=HTMLResponse)
def hauntsocial_page(request: Request):
    # Dan's approved explainer copy (Oct 25) — what HauntSocial is,
    # linked from the promo band and /signup.
    return templates.TemplateResponse(request, "hauntsocial.html", {"request": request})


# --------------------------------------------------------------- Haunt Chat
# Dan (Oct 27, 2026 — built STAGED for his preview, not yet shipped):
# ONE members-only chat room at /chat for HauntMap + HauntSocial.
# Members read the whole room and post; guests get a public teaser —
# the room shell, Frank's pinned welcome, and the latest few messages —
# behind a join gate. Fresh messages arrive by POLLING (4s, since-id,
# indexed id query, tiny payloads) — no websockets, so the single
# worker never holds a socket per visitor. Frank's welcome is pinned
# FROM CODE (a constant rendered at the top of the room), not a seeded
# row: it can never be deleted, buried, or duplicated by a re-seed.
CHAT_MAX_CHARS = 300
CHAT_ROOM_LIMIT = 100        # messages the room renders for a member
CHAT_TEASER_LIMIT = 5        # messages a guest may peek at
CHAT_MIN_GAP_S = 2           # min seconds between a member's posts
CHAT_BURST_LIMIT = 20        # posts per member per 10 minutes
CHAT_ADMIN_HANDLES = {"dan", "gethauntmap"}
FRANK_CHAT_WELCOME = (
    "Boo! 👻 Frank here — welcome to The Haunt Chat, haunters! This is "
    "our room to swap favorite haunts, plan Halloween events and "
    "parties, trade costume ideas, and argue over the best spooky "
    "music. Pull up a tombstone and say hi — just keep it friendly. 🎃")

_CHAT_SELECT = (
    "SELECT m.id, m.body, m.kind, m.reply_to, m.user_id, "
    "m.created_at, u.handle, "
    "p.display_name, p.avatar_choice, p.avatar_path "
    "FROM chat_messages m JOIN users u ON u.id = m.user_id "
    "LEFT JOIN profiles p ON p.user_id = u.id ")


def _chat_is_admin(member: dict | None) -> bool:
    """Chat moderation gate: the users.is_admin flag, or the two
    operator handles (Dan's own + the official brand account)."""
    return bool(member and (member.get("is_admin")
                            or member["handle"] in CHAT_ADMIN_HANDLES))


def _chat_view(row) -> dict:
    """One chat message as chat.html and the polling JSON render it."""
    return {"id": row["id"], "handle": row["handle"],
            "label": row["display_name"] or row["handle"],
            "avatar": _avatar_view(row["avatar_choice"],
                                   row["display_name"], row["handle"],
                                   row["avatar_path"]),
            "body": row["body"],
            "kind": row["kind"] or "text",
            "reply_to": row["reply_to"],
            "created_at": row["created_at"]}


def _shadow_muted_ids(conn) -> set[int]:
    """User ids currently shadow-muted (chat_mutes). A muted member's
    messages are visible ONLY to themselves and to admins — everyone
    else's room simply never contains them (brief §5)."""
    try:
        return {r["user_id"] for r in conn.execute(
            "SELECT user_id FROM chat_mutes").fetchall()}
    except sqlite3.OperationalError:
        return set()


def _chat_visibility(viewer: dict | None,
                     muted: set[int]) -> tuple[str, list]:
    """(SQL fragment, params) hiding shadow-muted authors from `viewer`.
    Admins see everything; a muted author still sees their own posts."""
    if not muted or _chat_is_admin(viewer):
        return "", []
    keep = [viewer["id"]] if viewer and viewer["id"] in muted else []
    hide = sorted(muted - set(keep))
    if not hide:
        return "", []
    marks = ", ".join("?" for _ in hide)
    return f" AND m.user_id NOT IN ({marks})", hide


def _chat_recent(limit: int, viewer: dict | None = None) -> list[dict]:
    """The newest `limit` live messages, oldest first (room order),
    shadow-mute filtered for `viewer`."""
    with get_conn(DB_PATH) as conn:
        frag, params = _chat_visibility(viewer, _shadow_muted_ids(conn))
        rows = conn.execute(
            _CHAT_SELECT + "WHERE m.deleted = 0" + frag +
            " ORDER BY m.id DESC LIMIT ?", (*params, limit)).fetchall()
    return [_chat_view(r) for r in reversed(rows)]


@app.get("/chat", response_class=HTMLResponse)
def chat_page(request: Request):
    member = current_member(request)
    ctx = {"request": request, "member": member,
           "frank_avatar": _avatar_view(FRANK_AVATAR_CHOICE, "Frank",
                                         FRANK_HANDLE),
           "frank_welcome": FRANK_CHAT_WELCOME,
           "chat_max": CHAT_MAX_CHARS}
    if member:
        msgs = _chat_recent(CHAT_ROOM_LIMIT, member)
        _attach_chat_extras(msgs, member)
        ctx.update({"messages": msgs,
                    "can_moderate": _chat_is_admin(member),
                    "teaser": False,
                    "pinned": _chat_pinned_view(member),
                    "mention_unseen": _mentions_unseen_count(member["id"]),
                    "games": _chat_games_for_room(member),
                    "stickers": list(TREAT_STICKERS),
                    "game_kinds": GAME_KIND_LABELS})
        if _chat_is_admin(member):
            ctx.update({"mod_log": _chat_mod_log_recent(30),
                        "muted_handles": _chat_muted_handles(),
                        "slow_mode_s": _chat_slow_mode_s()})
    else:
        msgs = _chat_recent(CHAT_TEASER_LIMIT)
        _attach_chat_extras(msgs, None)
        ctx.update({"messages": msgs,
                    "can_moderate": False, "teaser": True,
                    "pinned": None, "mention_unseen": 0})
    return templates.TemplateResponse(request, "chat.html", ctx)


@app.get("/api/chat/messages")
def chat_poll(request: Request, after: int = 0, before: int = 0):
    """The polling endpoint (members only). ?after=<last id seen>
    returns just the newer live messages plus the ids of messages a
    moderator deleted in the last 30 minutes ('gone'), so open rooms
    drop them without a reload. No `after` returns the room's latest
    CHAT_ROOM_LIMIT. ?before=<oldest id seen> pages one window of
    OLDER messages (quote jumps reach back past the room window).
    Indexed id lookups only — this runs every ~4s per open room and
    must stay cheap on the single worker."""
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    gone: list[int] = []
    with get_conn(DB_PATH) as conn:
        frag, vparams = _chat_visibility(member, _shadow_muted_ids(conn))
        if before > 0:
            rows = conn.execute(
                _CHAT_SELECT + "WHERE m.deleted = 0 AND m.id < ?" + frag +
                " ORDER BY m.id DESC LIMIT 100",
                (before, *vparams)).fetchall()
            msgs = [_chat_view(r) for r in reversed(rows)]
            _attach_chat_extras(msgs, member)
            resp = JSONResponse(
                {"messages": msgs, "gone": [],
                 "earliest_id": msgs[0]["id"] if msgs else before})
            resp.headers["Cache-Control"] = "no-store"
            return resp
        if after > 0:
            rows = conn.execute(
                _CHAT_SELECT + "WHERE m.deleted = 0 AND m.id > ?" + frag +
                " ORDER BY m.id ASC LIMIT 100", (after, *vparams)).fetchall()
            gone = [r["id"] for r in conn.execute(
                "SELECT id FROM chat_messages WHERE deleted = 1 "
                "AND id <= ? AND deleted_at > ?",
                (after, (datetime.now(timezone.utc)
                         - timedelta(minutes=30)).isoformat())).fetchall()]
            msgs = [_chat_view(r) for r in rows]
        else:
            msgs = _chat_recent(CHAT_ROOM_LIMIT, member)
    _attach_chat_extras(msgs, member)
    resp = JSONResponse({"messages": msgs, "gone": gone,
                         "latest_id": msgs[-1]["id"] if msgs else after})
    resp.headers["Cache-Control"] = "no-store"
    return resp


def _chat_rate_error(member: dict) -> JSONResponse | None:
    """The shared post-pipeline rate gate (base min gap, raised by
    admin slow mode, raised again for brand-new accounts — brief §5),
    read off the member's own chat_messages rows. Returns the 429
    response to send, or None when the post may proceed. Every way of
    putting a message in the room — text, sticker sends, poll
    creation — goes through this same gate."""
    now = datetime.now(timezone.utc)
    min_gap = max(CHAT_MIN_GAP_S, _chat_slow_mode_s())
    burst_limit = CHAT_BURST_LIMIT
    try:
        acct_age = (now - datetime.fromisoformat(
            member["created_at"])).total_seconds()
    except (ValueError, TypeError):
        acct_age = CHAT_NEW_ACCOUNT_S + 1
    if acct_age < CHAT_NEW_ACCOUNT_S:
        min_gap = max(min_gap, CHAT_NEW_ACCOUNT_GAP_S)
        burst_limit = CHAT_NEW_ACCOUNT_BURST
    with get_conn(DB_PATH) as conn:
        last = conn.execute(
            "SELECT created_at FROM chat_messages WHERE user_id = ? "
            "ORDER BY id DESC LIMIT 1", (member["id"],)).fetchone()
        if last:
            try:
                gap = (now - datetime.fromisoformat(
                    last["created_at"])).total_seconds()
            except ValueError:
                gap = min_gap
            if gap < min_gap:
                return JSONResponse(
                    {"ok": False,
                     "error": "Slow down — give it a few seconds "
                              "between messages."}, status_code=429)
        burst = conn.execute(
            "SELECT COUNT(*) AS n FROM chat_messages WHERE user_id = ? "
            "AND created_at > ?",
            (member["id"],
             (now - timedelta(minutes=10)).isoformat())).fetchone()["n"]
        if burst >= burst_limit:
            return JSONResponse(
                {"ok": False,
                 "error": "Whoa — that's a lot of messages. Take a "
                          "breather."}, status_code=429)
    return None


def _chat_insert_and_fanout(member: dict, body: str, kind: str = "text",
                            reply_to: int | None = None) -> dict:
    """Insert one room message, record its @mentions, and fan it out
    over the sockets with the shadow-mute rule. Returns the message
    view (extras attached). Caller has already validated the body,
    the reply target, and the rate gate."""
    now = datetime.now(timezone.utc)
    reply_author_id = None
    reply_blocked = False
    with get_conn(DB_PATH) as conn:
        cur = conn.execute(
            "INSERT INTO chat_messages (user_id, body, kind, reply_to, "
            "created_at) VALUES (?, ?, ?, ?, ?)",
            (member["id"], body, kind, reply_to, now.isoformat()))
        message_id = cur.lastrowid
        mentioned = (_record_mentions(conn, message_id, member, body)
                     if kind == "text" else [])
        if reply_to:
            orig = conn.execute(
                "SELECT user_id FROM chat_messages WHERE id = ?",
                (reply_to,)).fetchone()
            if orig and orig["user_id"] != member["id"]:
                reply_author_id = orig["user_id"]
                reply_blocked = _blocked_pair(
                    conn, member["id"], reply_author_id)
        conn.commit()
        row = conn.execute(
            _CHAT_SELECT + "WHERE m.id = ?", (message_id,)).fetchone()
        muted = member["id"] in _shadow_muted_ids(conn)
    view = _chat_view(row)
    _attach_chat_extras([view], member)
    # Real-time fan-out. A shadow-muted author's message goes only to
    # their own sockets and to admins — everyone else never sees it.
    _hub_broadcast_message(view, author_id=member["id"], shadow=muted)
    # Mentions that find you (brief §4): a targeted socket event to
    # each mentioned member who is online, following the same shadow
    # rule — an invisible message never pings its targets.
    for target in mentioned:
        if muted and target["id"] != member["id"] \
                and target["id"] not in _hub.admin_ids:
            continue
        _hub.broadcast(
            {"type": "mention",
             "mention": {"message_id": message_id,
                         "from": member["handle"],
                         "snippet": body[:80]},
             "count": _mentions_unseen_count(target["id"])},
            to_ids={target["id"]})
    # Wave 1 web push: the same events, for members who are NOT in
    # the room right now (notify_user skips anyone with a live
    # socket, anyone who hasn't opted in, and repeat triggers).
    # Blocks were already filtered by _record_mentions; the shadow
    # rule mirrors the socket fan-out above.
    online = set(_hub.conns)
    for target in mentioned:
        if muted and target["id"] != member["id"] \
                and target["id"] not in _hub.admin_ids:
            continue
        push_mod.notify_user(
            DB_PATH, target["id"], "mentions",
            f"💬 @{member['handle']} mentioned you in Haunt Chat",
            body[:120], url="/chat", ref=f"from-{member['id']}",
            online_ids=online)
    if reply_author_id and not reply_blocked and not muted:
        push_mod.notify_user(
            DB_PATH, reply_author_id, "replies",
            f"↩️ @{member['handle']} replied to you in Haunt Chat",
            body[:120], url="/chat", ref=f"from-{member['id']}",
            online_ids=online)
    return view


@app.post("/api/chat/messages")
async def chat_post(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    try:
        data = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    sticker = str(data.get("sticker") or "")
    reply_to = data.get("reply_to")
    if sticker:
        # Sticker send (brief §4): a treats sticker as its own
        # message, through the same rate gate as text.
        if sticker not in TREAT_STICKERS:
            return JSONResponse({"ok": False, "error": "unknown sticker"},
                                status_code=400)
        err = _chat_rate_error(member)
        if err:
            return err
        view = _chat_insert_and_fanout(member, sticker, kind="sticker")
        return JSONResponse({"ok": True, "message": view})
    body = str(data.get("body") or "").strip()
    if not body:
        return JSONResponse({"ok": False,
                             "error": "Write something first."},
                            status_code=400)
    if len(body) > CHAT_MAX_CHARS:
        return JSONResponse(
            {"ok": False,
             "error": f"Messages cap at {CHAT_MAX_CHARS} characters."},
            status_code=400)
    # Word filter (brief §5): family room — a filtered word never lands,
    # and the catch is written to the moderation audit log.
    hit = _chat_filter_hit(body)
    if hit:
        _chat_mod_log(member["id"], "filter", member["id"], None,
                      f"blocked word '{hit}' in: {body[:80]}")
        return JSONResponse(
            {"ok": False,
             "error": "Let's keep it family-friendly in here — that "
                      "one can't be posted."}, status_code=400)
    # Reply/quote target: must be a live message this member can see
    # (no quoting a shadow-muted member's post into public view).
    reply_id = None
    if reply_to:
        try:
            reply_id = int(reply_to)
        except (TypeError, ValueError):
            reply_id = None
        if reply_id is not None:
            with get_conn(DB_PATH) as conn:
                orig = conn.execute(
                    "SELECT user_id FROM chat_messages WHERE id = ? "
                    "AND deleted = 0", (reply_id,)).fetchone()
                if (orig is None
                        or (orig["user_id"] in _shadow_muted_ids(conn)
                            and orig["user_id"] != member["id"]
                            and not _chat_is_admin(member))):
                    return JSONResponse(
                        {"ok": False,
                         "error": "That message can't be quoted."},
                        status_code=400)
    err = _chat_rate_error(member)
    if err:
        return err
    view = _chat_insert_and_fanout(member, body, kind="text",
                                   reply_to=reply_id)
    return JSONResponse({"ok": True, "message": view})


@app.post("/api/chat/messages/{message_id}/delete")
def chat_delete(request: Request, message_id: int):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    if not _chat_is_admin(member):
        return JSONResponse({"error": "admins only"}, status_code=403)
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT id, user_id, body FROM chat_messages "
            "WHERE id = ? AND deleted = 0", (message_id,)).fetchone()
        if row is None:
            return JSONResponse({"error": "no such message"},
                                status_code=404)
        conn.execute(
            "UPDATE chat_messages SET deleted = 1, deleted_at = ? "
            "WHERE id = ?",
            (datetime.now(timezone.utc).isoformat(), message_id))
        conn.commit()
    _chat_mod_log(member["id"], "delete", row["user_id"], message_id,
                  (row["body"] or "")[:80])
    _hub.broadcast({"type": "gone", "id": message_id})
    return JSONResponse({"ok": True, "id": message_id})


# ------------------------------------------- Haunt Chat real-time upgrade
# Dan (Oct 27, 2026 — STAGED for his preview): the research brief's
# approved build. Native WebSockets inside this app on the ONE worker
# (in-memory registry — a second worker would silently split the room;
# see brief §3), the polling endpoint above stays as the automatic
# fallback, and reconnecting clients catch up through it. Ships with:
# presence + typing, the §5 safety pack (slow mode, server-side word
# filter, shadow-mute, audit log, per-message report, new-account
# friction), treat reactions, and the member-vs-member word games in
# the next section. Guests never open a socket — the teaser stays REST.
CHAT_NEW_ACCOUNT_S = 600        # "brand-new" window: 10 minutes
CHAT_NEW_ACCOUNT_GAP_S = 10     # min post gap inside that window
CHAT_NEW_ACCOUNT_BURST = 5      # burst cap inside that window
CHAT_SLOW_MODE_KEY = "chat_slow_mode_s"

# Family-room word filter. Curated common profanity/slurs, matched on
# whole tokens after a light leetspeak normalization, plus a squashed
# check for longer words so "f u c k"-style spacing doesn't slip by.
# Kept deliberately moderate to avoid Scunthorpe false positives.
CHAT_BANNED_WORDS = [
    "fuck", "fucking", "fucker", "shit", "shitty", "bitch", "bitches",
    "bastard", "asshole", "dickhead", "pussy", "whore", "slut",
    "nigger", "nigga", "faggot", "fag", "retard", "retarded",
    "cunt", "cock", "porn", "porno", "pornhub", "sexcam", "blowjob",
    "handjob", "jizz", "cumshot", "dildo", "hentai", "molest",
    "pedophile", "paedophile", "rapist", "suicide", "kys",
    "nazi", "hitler", "kkk",
]
_LEET_TABLE = str.maketrans({"0": "o", "1": "i", "3": "e", "4": "a",
                             "5": "s", "7": "t", "@": "a", "$": "s"})


def _chat_filter_hit(body: str) -> str | None:
    """The banned word found in `body`, or None. Whole-token match
    first. The squashed-letters pass (catches 'f u c k' spacing) only
    runs when the message carries the evasion signature — several
    single-letter tokens — or on words >= 5 chars, so innocent words
    that merely contain a banned substring (shiitake, assassin)
    never trip it."""
    norm = body.lower().translate(_LEET_TABLE)
    tokens = re.findall(r"[a-z]+", norm)
    token_set = set(tokens)
    squashed = "".join(tokens)
    spaced = sum(1 for t in tokens if len(t) == 1) >= 3
    for w in CHAT_BANNED_WORDS:
        if w in token_set:
            return w
        if w in squashed and (len(w) >= 5 or (spaced and len(w) >= 4)):
            return w
    return None


def _chat_slow_mode_s() -> int:
    """Admin slow mode: minimum seconds between anyone's posts,
    0 = off. Stored in social_meta so the mod panel can change it
    without a redeploy."""
    try:
        return max(0, min(60, int(_social_meta_get(CHAT_SLOW_MODE_KEY)
                                  or 0)))
    except (TypeError, ValueError):
        return 0


def _chat_mod_log(actor_id, action: str, target_user_id,
                  message_id, detail: str | None) -> None:
    """One moderation audit-log row (delete / mute / unmute / report /
    filter / slowmode). Best-effort: moderation never fails on it."""
    try:
        with get_conn(DB_PATH) as conn:
            conn.execute(
                "INSERT INTO chat_mod_log (actor_id, action, "
                "target_user_id, message_id, detail, created_at) "
                "VALUES (?, ?, ?, ?, ?, ?)",
                (actor_id, action, target_user_id, message_id,
                 (detail or "")[:300] or None,
                 datetime.now(timezone.utc).isoformat()))
            conn.commit()
    except sqlite3.OperationalError:
        pass


def _chat_mod_log_recent(limit: int) -> list[dict]:
    try:
        with get_conn(DB_PATH) as conn:
            rows = conn.execute(
                "SELECT l.id, l.action, l.detail, l.created_at, "
                "a.handle AS actor, t.handle AS target "
                "FROM chat_mod_log l "
                "LEFT JOIN users a ON a.id = l.actor_id "
                "LEFT JOIN users t ON t.id = l.target_user_id "
                "ORDER BY l.id DESC LIMIT ?", (limit,)).fetchall()
        return [dict(r) for r in rows]
    except sqlite3.OperationalError:
        return []


def _chat_muted_handles() -> list[str]:
    try:
        with get_conn(DB_PATH) as conn:
            rows = conn.execute(
                "SELECT u.handle FROM chat_mutes m "
                "JOIN users u ON u.id = m.user_id "
                "ORDER BY u.handle").fetchall()
        return [r["handle"] for r in rows]
    except sqlite3.OperationalError:
        return []


def _member_avatar_view(user_id: int) -> dict:
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT u.handle, p.display_name, p.avatar_choice, "
            "p.avatar_path FROM users u "
            "LEFT JOIN profiles p ON p.user_id = u.id WHERE u.id = ?",
            (user_id,)).fetchone()
    if row is None:
        return _avatar_view(None, None, "?")
    return _avatar_view(row["avatar_choice"], row["display_name"],
                        row["handle"], row["avatar_path"])


# ------------------------------------------------------------ the WS hub
# In-memory connection registry. This is correct ONLY because the app
# runs exactly one worker (Dockerfile pins --workers 1): every socket
# lives in this process, so a plain dict is the whole fan-out. The day
# a second worker/instance exists, this must move to a pub/sub
# backplane or Ably (brief §3/§4) — presence would otherwise split
# silently. Broadcasts are callable from any thread (sync endpoints run
# in the threadpool): pushes hop onto the captured event loop.
class _ChatConn:
    __slots__ = ("user_id", "handle", "queue")

    def __init__(self, user_id: int, handle: str, queue):
        self.user_id = user_id
        self.handle = handle
        self.queue = queue


class _ChatHub:
    def __init__(self):
        self.conns: dict[int, set] = {}
        self.admin_ids: set[int] = set()
        self.avatars: dict[int, dict] = {}
        self.typing: dict[int, tuple] = {}   # user_id -> (handle, expiry)
        self.loop = None

    def register(self, member: dict, avatar: dict) -> _ChatConn:
        conn = _ChatConn(member["id"], member["handle"],
                         asyncio.Queue(maxsize=200))
        self.conns.setdefault(member["id"], set()).add(conn)
        self.avatars[member["id"]] = avatar
        if _chat_is_admin(member):
            self.admin_ids.add(member["id"])
        return conn

    def unregister(self, conn: _ChatConn) -> None:
        room = self.conns.get(conn.user_id)
        if room:
            room.discard(conn)
            if not room:
                del self.conns[conn.user_id]
        self.typing.pop(conn.user_id, None)

    def _push(self, conn: _ChatConn, payload: dict) -> None:
        loop = self.loop
        if loop is None:
            return

        def _put():
            try:
                conn.queue.put_nowait(payload)
            except asyncio.QueueFull:
                # A wedged phone must never block a broadcast: drop its
                # oldest queued event, keep the newest.
                try:
                    conn.queue.get_nowait()
                    conn.queue.put_nowait(payload)
                except Exception:
                    pass

        try:
            loop.call_soon_threadsafe(_put)
        except RuntimeError:
            pass

    def broadcast(self, payload: dict, to_ids: set[int] | None = None):
        for uid, conns in list(self.conns.items()):
            if to_ids is not None and uid not in to_ids:
                continue
            for conn in list(conns):
                self._push(conn, payload)

    def typing_handles(self) -> list[str]:
        now = time.monotonic()
        stale = [uid for uid, (_, exp) in self.typing.items()
                 if exp <= now]
        for uid in stale:
            del self.typing[uid]
        return sorted(h for h, _ in self.typing.values())

    def presence_payload(self) -> dict:
        users = [{"handle": c.handle, "avatar": self.avatars.get(uid)}
                 for uid, conns in self.conns.items()
                 for c in list(conns)[:1]]
        users.sort(key=lambda u: u["handle"])
        return {"type": "presence", "count": len(users),
                "users": users, "typing": self.typing_handles()}

    def broadcast_presence(self) -> None:
        self.broadcast(self.presence_payload())

    def set_typing(self, member: dict, on: bool) -> None:
        if on:
            self.typing[member["id"]] = (member["handle"],
                                         time.monotonic() + 4)
        else:
            self.typing.pop(member["id"], None)
        self.broadcast({"type": "typing",
                        "handles": self.typing_handles()})


_hub = _ChatHub()


def _hub_broadcast_message(view: dict, author_id: int,
                           shadow: bool) -> None:
    """Fan a new message out over the sockets. Shadow-muted authors'
    messages go only to their own sockets and to admins (the REST
    paths filter the same way — see _chat_visibility)."""
    payload = {"type": "message", "message": view}
    if shadow:
        _hub.broadcast(payload,
                       to_ids={author_id} | set(_hub.admin_ids))
    else:
        _hub.broadcast(payload)


async def _ws_send_loop(websocket: WebSocket, queue) -> None:
    while True:
        payload = await queue.get()
        await websocket.send_json(payload)


async def _ws_ping_loop(queue) -> None:
    # Cloudflare kills idle WebSockets at ~100s; a frame every 30s
    # keeps the connection warm (brief §2.1). Browsers ignore the
    # unknown message type.
    while True:
        await asyncio.sleep(30)
        try:
            queue.put_nowait({"type": "ping"})
        except asyncio.QueueFull:
            pass


@app.websocket("/ws/chat")
async def chat_ws(websocket: WebSocket):
    member = current_member(websocket)
    if not member:
        await websocket.close(code=4401)
        return
    await websocket.accept()
    _hub.loop = asyncio.get_running_loop()
    conn = _hub.register(member, _member_avatar_view(member["id"]))
    sender = asyncio.create_task(_ws_send_loop(websocket, conn.queue))
    pinger = asyncio.create_task(_ws_ping_loop(conn.queue))
    _hub.broadcast_presence()

    async def _pump():
        while True:
            data = await websocket.receive_json()
            if not isinstance(data, dict):
                continue
            if data.get("type") == "typing":
                _hub.set_typing(member, bool(data.get("on")))

    pump = asyncio.create_task(_pump())
    try:
        await asyncio.wait({pump, sender},
                           return_when=asyncio.FIRST_COMPLETED)
    finally:
        for task in (pump, sender, pinger):
            task.cancel()
        _hub.unregister(conn)
        _hub.broadcast_presence()
        _hub.broadcast({"type": "typing",
                        "handles": _hub.typing_handles()})


# ------------------------------------------------------------- reactions
def _reactions_map(conn, message_ids: list[int],
                   viewer_id: int | None) -> dict:
    """{message_id: {"counts": {sticker: n}, "by": {sticker: [handles]},
    "mine": [stickers the viewer stuck]}} for a batch of messages."""
    out = {mid: {"counts": {}, "by": {}, "mine": []}
           for mid in message_ids}
    if not message_ids:
        return out
    marks = ", ".join("?" for _ in message_ids)
    try:
        rows = conn.execute(
            "SELECT r.message_id, r.sticker, r.user_id, u.handle "
            "FROM chat_reactions r JOIN users u ON u.id = r.user_id "
            f"WHERE r.message_id IN ({marks})", message_ids).fetchall()
    except sqlite3.OperationalError:
        return out
    for r in rows:
        entry = out[r["message_id"]]
        entry["counts"][r["sticker"]] = \
            entry["counts"].get(r["sticker"], 0) + 1
        entry["by"].setdefault(r["sticker"], []).append(r["handle"])
        if viewer_id and r["user_id"] == viewer_id:
            entry["mine"].append(r["sticker"])
    return out


def _attach_reactions(msgs: list[dict],
                      viewer_id: int | None) -> list[dict]:
    if not msgs:
        return msgs
    with get_conn(DB_PATH) as conn:
        rmap = _reactions_map(conn, [m["id"] for m in msgs], viewer_id)
    for m in msgs:
        m["reactions"] = rmap.get(
            m["id"], {"counts": {}, "by": {}, "mine": []})
    return msgs


# ------------------------------------------ Haunt Chat Wave 0 quick wins
# Dan (Oct 27, 2026 — benchmark brief §4/§5, STAGED for preview):
# @mentions that find you, reply/quote, room polls, pin-a-message,
# sticker sends, and Frank announcing new listings. Everything rides
# the existing WS + REST model and the same visibility rules: a
# shadow-muted author's content (mentions, quote snippets, poll
# votes) stays invisible to everyone but themselves and admins.
CHAT_PIN_KEY = "chat_pinned_message_id"
CHAT_POLL_MAX_OPTIONS = 4
CHAT_POLL_OPTION_MAX = 60
FRANK_NEWS_MIN_GAP_S = 600      # at most one listing shout per 10 min
FRANK_NEWS_HOURLY_CAP = 6       # ...and at most 6 per hour, batched
FRANK_NEWS_LAST_KEY = "chat_frank_news_last"
FRANK_NEWS_PENDING_KEY = "chat_frank_news_pending"
FRANK_NEWS_HOUR_KEY = "chat_frank_news_hour"
_MENTION_RE = re.compile(r"@([A-Za-z0-9_]{2,30})")


def _blocked_pair(conn, a_id: int, b_id: int) -> bool:
    """True when a block exists in either direction between two
    members (the games layer's rule, reused for mentions)."""
    try:
        return conn.execute(
            "SELECT 1 FROM blocks WHERE (blocker_id = ? AND "
            "blocked_id = ?) OR (blocker_id = ? AND blocked_id = ?)",
            (a_id, b_id, b_id, a_id)).fetchone() is not None
    except sqlite3.OperationalError:
        return False


def _poll_view(conn, poll, viewer: dict | None) -> dict:
    """A poll as the room renders it: per-option counts (shadow-mute
    filtered for the viewer, like messages), the viewer's own vote,
    and the closed flag. Vote rows from muted members are excluded
    from other members' counts — a muted member still sees their own
    vote marked, admins see true totals."""
    try:
        options = json.loads(poll["options"])
    except (ValueError, TypeError):
        options = []
    muted = _shadow_muted_ids(conn)
    hide: set[int] = set()
    if muted and not _chat_is_admin(viewer):
        hide = muted - ({viewer["id"]} if viewer else set())
    counts = [0] * len(options)
    total = 0
    my_vote = None
    try:
        rows = conn.execute(
            "SELECT user_id, option_idx FROM chat_poll_votes "
            "WHERE poll_id = ?", (poll["id"],)).fetchall()
    except sqlite3.OperationalError:
        rows = []
    for r in rows:
        if viewer and r["user_id"] == viewer["id"]:
            my_vote = r["option_idx"]
        if r["user_id"] in hide:
            continue
        if 0 <= r["option_idx"] < len(options):
            counts[r["option_idx"]] += 1
            total += 1
    return {"id": poll["id"], "question": poll["question"],
            "options": [{"text": t, "votes": counts[i]}
                        for i, t in enumerate(options)],
            "total": total, "my_vote": my_vote,
            "closed": bool(poll["closed"]),
            "message_id": poll["message_id"]}


def _attach_chat_extras(msgs: list[dict],
                        viewer: dict | None) -> list[dict]:
    """Everything a message render needs beyond the row itself:
    reactions, the @handles it mentions, its reply-quote target
    (snippet, or 'gone' when the original is deleted or invisible to
    this viewer), its poll card, and a 👉 link on Frank's listing
    announcements."""
    _attach_reactions(msgs, viewer["id"] if viewer else None)
    for m in msgs:
        m.setdefault("mentions", [])
        m.setdefault("reply", None)
        m.setdefault("poll", None)
        m.setdefault("link", None)
    if not msgs:
        return msgs
    ids = [m["id"] for m in msgs]
    marks = ", ".join("?" for _ in ids)
    with get_conn(DB_PATH) as conn:
        muted = _shadow_muted_ids(conn)
        # Mentions per message (handles only — highlighting is a
        # render concern).
        try:
            for r in conn.execute(
                    "SELECT mn.message_id, u.handle FROM chat_mentions mn "
                    "JOIN users u ON u.id = mn.mentioned_user_id "
                    f"WHERE mn.message_id IN ({marks})", ids).fetchall():
                for m in msgs:
                    if m["id"] == r["message_id"]:
                        m["mentions"].append(r["handle"])
        except sqlite3.OperationalError:
            pass
        # Reply targets in one pass.
        reply_ids = sorted({m["reply_to"] for m in msgs if m["reply_to"]})
        if reply_ids:
            rmarks = ", ".join("?" for _ in reply_ids)
            originals = {}
            for r in conn.execute(
                    _CHAT_SELECT + f"WHERE m.id IN ({rmarks})",
                    reply_ids).fetchall():
                originals[r["id"]] = r
            for m in msgs:
                if not m["reply_to"]:
                    continue
                orig = originals.get(m["reply_to"])
                gone = (
                    orig is None
                    or (orig["user_id"] in muted
                        and not _chat_is_admin(viewer)
                        and not (viewer
                                 and viewer["id"] == orig["user_id"])))
                if gone:
                    m["reply"] = {"id": m["reply_to"], "gone": True}
                else:
                    snippet = (orig["body"] or "").strip()
                    if orig["kind"] == "sticker":
                        snippet = orig["body"]
                    elif orig["kind"] == "poll":
                        snippet = "📊 " + snippet
                    m["reply"] = {
                        "id": orig["id"], "handle": orig["handle"],
                        "snippet": snippet[:80], "gone": False}
        # Poll cards for kind='poll' messages.
        poll_ids = [m["id"] for m in msgs if m["kind"] == "poll"]
        if poll_ids:
            pmarks = ", ".join("?" for _ in poll_ids)
            try:
                prows = conn.execute(
                    f"SELECT * FROM chat_polls WHERE message_id IN "
                    f"({pmarks})", poll_ids).fetchall()
            except sqlite3.OperationalError:
                prows = []
            by_msg = {p["message_id"]: p for p in prows}
            for m in msgs:
                if m["id"] in by_msg:
                    m["poll"] = _poll_view(conn, by_msg[m["id"]], viewer)
        # Frank's listing announcements carry a tappable link: the
        # body ends with the entry's /d/<id> path.
        for m in msgs:
            if m["handle"] == FRANK_HANDLE:
                hit = re.search(r"(/d/\d+)\s*$", (m["body"] or "").strip())
                if hit:
                    m["link"] = hit.group(1)
    return msgs


def _record_mentions(conn, message_id: int, author: dict,
                     body: str) -> list[dict]:
    """Persist @mentions found in a fresh message. Skips: the author
    themselves, unknown/inactive handles, duplicates, and any pair
    with a block in either direction (blocking suppresses mentions,
    brief §4). Returns the members to live-notify."""
    handles = []
    for h in _MENTION_RE.findall(body or ""):
        h = h.lower()
        if h not in handles:
            handles.append(h)
    out = []
    now = _now_iso()
    for h in handles[:5]:
        if h == author["handle"]:
            continue
        row = conn.execute(
            "SELECT id, handle FROM users WHERE handle = ? "
            "AND status = 'active'", (h,)).fetchone()
        if row is None or row["id"] == author["id"]:
            continue
        if _blocked_pair(conn, author["id"], row["id"]):
            continue
        try:
            conn.execute(
                "INSERT OR IGNORE INTO chat_mentions (message_id, "
                "mentioned_user_id, seen, created_at) VALUES (?, ?, 0, ?)",
                (message_id, row["id"], now))
        except sqlite3.OperationalError:
            continue
        out.append({"id": row["id"], "handle": row["handle"]})
    return out


def _mentions_unseen_count(user_id: int) -> int:
    try:
        with get_conn(DB_PATH) as conn:
            u = conn.execute(
                "SELECT id, handle, is_admin FROM users WHERE id = ?",
                (user_id,)).fetchone()
            viewer = (dict(u) if u else
                      {"id": user_id, "handle": "", "is_admin": 0})
            frag, params = _chat_visibility(
                viewer, _shadow_muted_ids(conn))
            row = conn.execute(
                "SELECT COUNT(*) AS n FROM chat_mentions mn "
                "JOIN chat_messages m ON m.id = mn.message_id "
                "WHERE mn.mentioned_user_id = ? AND mn.seen = 0 "
                "AND m.deleted = 0" + frag,
                (user_id, *params)).fetchone()
        return row["n"] if row else 0
    except sqlite3.OperationalError:
        return 0


def _chat_pinned_view(viewer: dict | None) -> dict | None:
    """The admin-pinned message (pin-a-message), or None. Frank's
    welcome is separate and always stands. A pinned message whose
    author is shadow-muted shows only to the author and admins."""
    raw = _social_meta_get(CHAT_PIN_KEY)
    if not raw:
        return None
    try:
        mid = int(raw)
    except (TypeError, ValueError):
        return None
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            _CHAT_SELECT + "WHERE m.id = ? AND m.deleted = 0",
            (mid,)).fetchone()
        if row is None:
            return None
        if (row["user_id"] in _shadow_muted_ids(conn)
                and not _chat_is_admin(viewer)
                and not (viewer and viewer["id"] == row["user_id"])):
            return None
    view = _chat_view(row)
    _attach_chat_extras([view], viewer)
    return view


@app.post("/api/chat/messages/{message_id}/react")
async def chat_react(request: Request, message_id: int):
    """Toggle one treat sticker on a message (brief §6 #1). One row per
    (message, member, sticker): re-tapping removes it."""
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    try:
        data = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    sticker = str(data.get("sticker") or "")
    if sticker not in TREAT_STICKERS:
        return JSONResponse({"ok": False, "error": "unknown sticker"},
                            status_code=400)
    now = datetime.now(timezone.utc).isoformat()
    with get_conn(DB_PATH) as conn:
        msg = conn.execute(
            "SELECT user_id FROM chat_messages "
            "WHERE id = ? AND deleted = 0", (message_id,)).fetchone()
        if msg is None:
            return JSONResponse({"ok": False, "error": "no such message"},
                                status_code=404)
        if (msg["user_id"] in _shadow_muted_ids(conn)
                and not _chat_is_admin(member)
                and msg["user_id"] != member["id"]):
            return JSONResponse({"ok": False, "error": "no such message"},
                                status_code=404)
        existing = conn.execute(
            "SELECT 1 FROM chat_reactions WHERE message_id = ? "
            "AND user_id = ? AND sticker = ?",
            (message_id, member["id"], sticker)).fetchone()
        if existing:
            conn.execute(
                "DELETE FROM chat_reactions WHERE message_id = ? "
                "AND user_id = ? AND sticker = ?",
                (message_id, member["id"], sticker))
        else:
            conn.execute(
                "INSERT INTO chat_reactions (message_id, user_id, "
                "sticker, created_at) VALUES (?, ?, ?, ?)",
                (message_id, member["id"], sticker, now))
        conn.commit()
        summary = _reactions_map(conn, [message_id], member["id"])[message_id]
    _hub.broadcast({"type": "reaction", "message_id": message_id,
                    "counts": summary["counts"], "by": summary["by"]})
    return JSONResponse({"ok": True, "reactions": summary})


@app.post("/api/chat/messages/{message_id}/report")
def chat_report(request: Request, message_id: int):
    """Per-message report: lands in the shared reports queue (the admin
    surface the wall reports already use) AND in the chat audit log."""
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    now = datetime.now(timezone.utc).isoformat()
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT user_id, body FROM chat_messages "
            "WHERE id = ? AND deleted = 0", (message_id,)).fetchone()
        if row is None:
            return JSONResponse({"ok": False, "error": "no such message"},
                                status_code=404)
        conn.execute(
            "INSERT INTO reports (reporter_user_id, target_type, "
            "target_id, reason, created_at) "
            "VALUES (?, 'chat_message', ?, ?, ?)",
            (member["id"], message_id,
             f"chat message by user {row['user_id']}", now))
        conn.commit()
    _chat_mod_log(member["id"], "report", row["user_id"], message_id,
                  (row["body"] or "")[:80])
    return JSONResponse({"ok": True})


# ------------------------------------------- Wave 0: mentions endpoints
@app.get("/api/chat/mentions")
def chat_mentions(request: Request):
    """The mentions panel (brief §4, 'inbox-lite'): the member's
    latest mentions on messages they can actually see, newest first,
    plus the unseen count."""
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    with get_conn(DB_PATH) as conn:
        frag, vparams = _chat_visibility(member, _shadow_muted_ids(conn))
        rows = conn.execute(
            "SELECT mn.message_id, mn.seen, mn.created_at, "
            "u.handle AS from_handle, m.body, m.kind "
            "FROM chat_mentions mn "
            "JOIN chat_messages m ON m.id = mn.message_id "
            "JOIN users u ON u.id = m.user_id "
            "WHERE mn.mentioned_user_id = ? AND m.deleted = 0" + frag +
            " ORDER BY mn.message_id DESC LIMIT 25",
            (member["id"], *vparams)).fetchall()
    items = [{"message_id": r["message_id"],
              "from": r["from_handle"],
              "snippet": (r["body"] or "")[:80],
              "seen": bool(r["seen"]),
              "created_at": r["created_at"]} for r in rows]
    return JSONResponse(
        {"mentions": items,
         "unseen": _mentions_unseen_count(member["id"])})


@app.post("/api/chat/mentions/seen")
def chat_mentions_seen(request: Request):
    """Opening the mentions panel marks them seen (the records stay —
    the panel keeps listing them)."""
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    with get_conn(DB_PATH) as conn:
        conn.execute(
            "UPDATE chat_mentions SET seen = 1 "
            "WHERE mentioned_user_id = ? AND seen = 0", (member["id"],))
        conn.commit()
    return JSONResponse({"ok": True, "unseen": 0})


# ---------------------------------------------- Wave 0: polls endpoints
@app.post("/api/chat/polls")
async def chat_poll_create(request: Request):
    """Room polls are admin/Frank-created (brief §4; the family-room
    posture — an open poll firehose is a spam surface). The poll lives
    in the room as a kind='poll' message so it orders, catches up,
    and teasers like any other message."""
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    if not _chat_is_admin(member):
        return JSONResponse({"error": "admins only"}, status_code=403)
    try:
        data = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    question = str(data.get("question") or "").strip()
    raw_options = data.get("options") or []
    options: list[str] = []
    seen_opts: set[str] = set()
    for o in raw_options:
        o = str(o or "").strip()[:CHAT_POLL_OPTION_MAX]
        if o and o.lower() not in seen_opts:
            options.append(o)
            seen_opts.add(o.lower())
    if not question or len(question) > CHAT_MAX_CHARS:
        return JSONResponse(
            {"ok": False, "error": "Give the poll a question "
                                   f"(up to {CHAT_MAX_CHARS} characters)."},
            status_code=400)
    if not (2 <= len(options) <= CHAT_POLL_MAX_OPTIONS):
        return JSONResponse(
            {"ok": False,
             "error": f"Polls need 2–{CHAT_POLL_MAX_OPTIONS} options."},
            status_code=400)
    hit = _chat_filter_hit(question + " " + " ".join(options))
    if hit:
        _chat_mod_log(member["id"], "filter", member["id"], None,
                      f"blocked word '{hit}' in poll: {question[:60]}")
        return JSONResponse(
            {"ok": False,
             "error": "Let's keep it family-friendly in here — that "
                      "one can't be posted."}, status_code=400)
    # Validation errors (incl. the one-open-poll rule) outrank the
    # rate gate; the open-poll check repeats inside the write
    # transaction below, which stays authoritative.
    with get_conn(DB_PATH) as conn:
        already_open = conn.execute(
            "SELECT id FROM chat_polls WHERE closed = 0").fetchone()
    if already_open is not None:
        return JSONResponse(
            {"ok": False,
             "error": "A poll is already open — close it before "
                      "starting another."}, status_code=400)
    err = _chat_rate_error(member)
    if err:
        return err
    now = datetime.now(timezone.utc)
    with get_conn(DB_PATH) as conn:
        open_poll = conn.execute(
            "SELECT id FROM chat_polls WHERE closed = 0").fetchone()
        if open_poll is not None:
            return JSONResponse(
                {"ok": False,
                 "error": "A poll is already open — close it before "
                          "starting another."}, status_code=400)
        cur = conn.execute(
            "INSERT INTO chat_messages (user_id, body, kind, reply_to, "
            "created_at) VALUES (?, ?, 'poll', NULL, ?)",
            (member["id"], question, now.isoformat()))
        message_id = cur.lastrowid
        pcur = conn.execute(
            "INSERT INTO chat_polls (message_id, question, options, "
            "created_by, closed, created_at) VALUES (?, ?, ?, ?, 0, ?)",
            (message_id, question, json.dumps(options),
             member["id"], now.isoformat()))
        poll_id = pcur.lastrowid
        conn.commit()
        row = conn.execute(
            _CHAT_SELECT + "WHERE m.id = ?", (message_id,)).fetchone()
        prow = conn.execute("SELECT * FROM chat_polls WHERE id = ?",
                            (poll_id,)).fetchone()
        poll_view = _poll_view(conn, prow, member)
    view = _chat_view(row)
    _attach_chat_extras([view], member)
    view["poll"] = poll_view
    _hub_broadcast_message(view, author_id=member["id"], shadow=False)
    _chat_mod_log(member["id"], "poll", None, message_id,
                  f"poll opened: {question[:60]}")
    return JSONResponse({"ok": True, "message": view, "poll": poll_view})


@app.post("/api/chat/polls/{poll_id}/vote")
async def chat_poll_vote(request: Request, poll_id: int):
    """One vote per member; voting again moves the vote. Counts ride
    back over the socket so open rooms watch the bars move live."""
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    try:
        data = await request.json()
        option_idx = int(data.get("option_idx"))
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    with get_conn(DB_PATH) as conn:
        poll = conn.execute("SELECT * FROM chat_polls WHERE id = ?",
                            (poll_id,)).fetchone()
        if poll is None:
            return JSONResponse({"ok": False, "error": "no such poll"},
                                status_code=404)
        if poll["closed"]:
            return JSONResponse({"ok": False,
                                 "error": "That poll is closed."},
                                status_code=400)
        try:
            n_options = len(json.loads(poll["options"]))
        except (ValueError, TypeError):
            n_options = 0
        if not (0 <= option_idx < n_options):
            return JSONResponse({"ok": False, "error": "bad option"},
                                status_code=400)
        conn.execute(
            "INSERT INTO chat_poll_votes (poll_id, user_id, option_idx, "
            "created_at) VALUES (?, ?, ?, ?) ON CONFLICT(poll_id, "
            "user_id) DO UPDATE SET option_idx = excluded.option_idx, "
            "created_at = excluded.created_at",
            (poll_id, member["id"], option_idx,
             datetime.now(timezone.utc).isoformat()))
        conn.commit()
        mine = _poll_view(conn, poll, member)
        public = _poll_view(conn, poll, None)
    _hub.broadcast({"type": "poll", "poll_id": poll_id, "poll": public})
    return JSONResponse({"ok": True, "poll": mine})


@app.post("/api/chat/polls/{poll_id}/close")
def chat_poll_close(request: Request, poll_id: int):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    if not _chat_is_admin(member):
        return JSONResponse({"error": "admins only"}, status_code=403)
    with get_conn(DB_PATH) as conn:
        poll = conn.execute("SELECT * FROM chat_polls WHERE id = ?",
                            (poll_id,)).fetchone()
        if poll is None:
            return JSONResponse({"ok": False, "error": "no such poll"},
                                status_code=404)
        conn.execute(
            "UPDATE chat_polls SET closed = 1, closed_at = ? WHERE id = ?",
            (datetime.now(timezone.utc).isoformat(), poll_id))
        conn.commit()
        poll = conn.execute("SELECT * FROM chat_polls WHERE id = ?",
                            (poll_id,)).fetchone()
        public = _poll_view(conn, poll, None)
    _hub.broadcast({"type": "poll", "poll_id": poll_id, "poll": public})
    _chat_mod_log(member["id"], "poll_close", None, poll["message_id"],
                  f"poll closed: {(poll['question'] or '')[:60]}")
    return JSONResponse({"ok": True, "poll": public})


# ------------------------------------ Wave 0: pin-a-message endpoints
@app.post("/api/chat/admin/pin")
async def chat_admin_pin(request: Request):
    """Pin one message under Frank's welcome (brief §4). One pin at
    a time; pinning another replaces it."""
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    if not _chat_is_admin(member):
        return JSONResponse({"error": "admins only"}, status_code=403)
    try:
        data = await request.json()
        message_id = int(data.get("message_id"))
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT user_id, body FROM chat_messages WHERE id = ? "
            "AND deleted = 0", (message_id,)).fetchone()
    if row is None:
        return JSONResponse({"ok": False, "error": "no such message"},
                            status_code=404)
    _social_meta_set(CHAT_PIN_KEY, str(message_id))
    _chat_mod_log(member["id"], "pin", row["user_id"], message_id,
                  (row["body"] or "")[:80])
    # The broadcast carries the public view of the pin (a muted
    # author's pin resolves to None publicly; admins see the real
    # one on next load — the server render is authoritative).
    _hub.broadcast({"type": "pin",
                    "pinned": _chat_pinned_view(None),
                    "pinned_id": message_id})
    return JSONResponse({"ok": True, "pinned_id": message_id,
                         "pinned": _chat_pinned_view(member)})


@app.post("/api/chat/admin/unpin")
def chat_admin_unpin(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    if not _chat_is_admin(member):
        return JSONResponse({"error": "admins only"}, status_code=403)
    _social_meta_set(CHAT_PIN_KEY, "")
    _chat_mod_log(member["id"], "unpin", None, None, "pin cleared")
    _hub.broadcast({"type": "pin", "pinned": None, "pinned_id": None})
    return JSONResponse({"ok": True})


# -------------------------------------------------------- admin endpoints
@app.get("/api/chat/modlog")
def chat_modlog(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    if not _chat_is_admin(member):
        return JSONResponse({"error": "admins only"}, status_code=403)
    pinned_raw = _social_meta_get(CHAT_PIN_KEY)
    return JSONResponse({"entries": _chat_mod_log_recent(50),
                         "muted": _chat_muted_handles(),
                         "slow_mode_s": _chat_slow_mode_s(),
                         "pinned_id": int(pinned_raw) if pinned_raw
                         and pinned_raw.isdigit() else None})


async def _chat_admin_target(request: Request):
    """(member, target row) for the mute/unmute endpoints, or a
    JSONResponse error in place of the target."""
    member = current_member(request)
    if not member:
        return None, JSONResponse({"error": "members only"},
                                  status_code=401)
    if not _chat_is_admin(member):
        return None, JSONResponse({"error": "admins only"},
                                  status_code=403)
    try:
        data = await request.json()
    except Exception:
        return None, JSONResponse({"ok": False, "error": "bad request"},
                                  status_code=400)
    handle = str(data.get("handle") or "").strip().lower().lstrip("@")
    with get_conn(DB_PATH) as conn:
        row = conn.execute("SELECT id, handle FROM users WHERE handle = ?",
                           (handle,)).fetchone()
    if row is None:
        return None, JSONResponse({"ok": False,
                                   "error": "no such member"},
                                  status_code=404)
    return member, dict(row)


@app.post("/api/chat/admin/mute")
async def chat_admin_mute(request: Request):
    """Shadow-mute a member: their posts keep 'working' for them but
    reach only themselves and admins. Silent by design."""
    member, target = await _chat_admin_target(request)
    if member is None:
        return target
    with get_conn(DB_PATH) as conn:
        conn.execute(
            "INSERT OR IGNORE INTO chat_mutes (user_id, muted_by, "
            "created_at) VALUES (?, ?, ?)",
            (target["id"], member["id"],
             datetime.now(timezone.utc).isoformat()))
        conn.commit()
    _chat_mod_log(member["id"], "mute", target["id"], None,
                  f"shadow-muted @{target['handle']}")
    return JSONResponse({"ok": True, "muted": _chat_muted_handles()})


@app.post("/api/chat/admin/unmute")
async def chat_admin_unmute(request: Request):
    member, target = await _chat_admin_target(request)
    if member is None:
        return target
    with get_conn(DB_PATH) as conn:
        conn.execute("DELETE FROM chat_mutes WHERE user_id = ?",
                     (target["id"],))
        conn.commit()
    _chat_mod_log(member["id"], "unmute", target["id"], None,
                  f"unmuted @{target['handle']}")
    return JSONResponse({"ok": True, "muted": _chat_muted_handles()})


@app.post("/api/chat/admin/slowmode")
async def chat_admin_slowmode(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    if not _chat_is_admin(member):
        return JSONResponse({"error": "admins only"}, status_code=403)
    try:
        data = await request.json()
        seconds = max(0, min(60, int(data.get("seconds"))))
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    _social_meta_set(CHAT_SLOW_MODE_KEY, str(seconds))
    _chat_mod_log(member["id"], "slowmode", None, None,
                  f"slow mode set to {seconds}s")
    return JSONResponse({"ok": True, "slow_mode_s": seconds})


# ------------------------------------------------------------------ games
# Member-vs-member word games (Dan-picked, brief §7): Ghost Word,
# Word Unscramble Duel, Word Chain: Haunt Edition. All turn-based and
# async-safe — a game row is JSON state in chat_games, moves ride the
# same REST+WS paths as chat, and results are announced by Frank as
# real chat messages and tallied onto profiles. No wagering, no side
# channels, blocking blocks challenges, profiles can opt out.
GAME_KIND_LABELS = {
    "ghost_word": "Ghost Word 👻",
    "unscramble": "Word Unscramble Duel 🔤",
    "word_chain": "Word Chain: Haunt Edition 🔗",
}
CHAT_CHALLENGE_TTL_S = 120       # accept window on an invite card
CHAT_CHALLENGE_HOURLY_CAP = 10   # invites sent per member per hour
GHOST_MAX_WRONG = 8              # wrong guesses that complete the ghost
UNSCRAMBLE_ROUNDS = 5
CHAIN_TURN_S = 45                # seconds per Word Chain turn
CHAIN_MAX_STRIKES = 2

HALLOWEEN_WORDS = [
    "pumpkin", "ghost", "witch", "vampire", "werewolf", "skeleton",
    "haunted", "costume", "candy", "spider", "cobweb", "cauldron",
    "graveyard", "tombstone", "mummy", "zombie", "monster", "dracula",
    "raven", "goblin", "ghoul", "phantom", "specter", "warlock",
    "wizard", "potion", "spellbook", "curse", "coffin", "crypt",
    "dungeon", "lantern", "broomstick", "blackcat", "fullmoon",
    "howling", "creepy", "spooky", "eerie", "fright", "terror",
    "haunting", "poltergeist", "seance", "ouija", "tarot", "crystal",
    "candle", "shadow", "midnight", "october", "autumn", "harvest",
    "scarecrow", "hayride", "cornmaze", "bonfire", "cider", "caramel",
    "apple", "treat", "trick", "mask", "cape", "fangs", "claws",
    "wings", "broom", "wand", "hat", "cloak", "gown", "makeup",
    "facepaint", "wig", " horns", "tail", "pumpkins", "ghosts",
    "witches", "spiders", "bats", "owls", "cats", "rats", "snakes",
    "frogs", "toads", "newts", "wolves", "bears", "crows", "webs",
    "skeletons", "mummies", "zombies", "vampires", "goblins",
    "hauntedhouse", "cemetery", "mausoleum", "headstone", "epitaph",
    "funeral", "burial", "coffins", "chains", "locks", "keys",
    "doors", "windows", "attic", "basement", "cellar", "stairs",
    "hallway", "mirror", "portrait", "chandelier", "fireplace",
    "thunder", "lightning", "storm", "rain", "wind", "fog",
    "moonlight", "starlight", "darkness", "silence", "whisper",
    "scream", "giggle", "cackle", "moan", "groan", "rattle",
    "scratch", "knock", "creak", "thump", "howl", "hoot",
    "pumpkinking", "jackolantern", "nightmare", "daydream",
    "frankenstein", "bride", "groom", "wedding", "party",
    "parade", "festival", "carnival", "circus", "magic", "magician",
]
# Normalize the bank: lowercase alpha only, no dupes, no strays.
HALLOWEEN_WORDS = sorted({w.strip() for w in HALLOWEEN_WORDS
                          if w.strip().isalpha() and len(w.strip()) >= 3})
_HALLOWEEN_SET = set(HALLOWEEN_WORDS)
_GAME_WORD_POOL = [w for w in HALLOWEEN_WORDS if len(w) >= 5]

_WORDLIST_CACHE: set | None = None


def _wordlist_set() -> set:
    """Bundled dictionary for Word Chain validation (app/
    chat_wordlist.txt, ~150k common words) plus the Halloween bank,
    which always validates (and scores the bonus). Loaded lazily,
    once, off the request path's hot loop."""
    global _WORDLIST_CACHE
    if _WORDLIST_CACHE is None:
        words = set(_HALLOWEEN_SET)
        try:
            text = (Path(__file__).parent / "chat_wordlist.txt") \
                .read_text(encoding="utf-8")
            words |= {w.strip() for w in text.splitlines() if w.strip()}
        except OSError:
            pass
        _WORDLIST_CACHE = words
    return _WORDLIST_CACHE


# Pairings that declined a challenge: (challenger_id, opponent_id) —
# their invites stay muted for the rest of the server run (brief §7.4).
_DECLINE_MUTES: set = set()


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _frank_announce(body: str) -> None:
    """Post a system announcement as Frank (the host account) and fan
    it out over the sockets. Silent no-op if Frank's row is absent."""
    try:
        with get_conn(DB_PATH) as conn:
            frank = conn.execute(
                "SELECT id FROM users WHERE handle = ?",
                (FRANK_HANDLE,)).fetchone()
            if frank is None:
                return
            cur = conn.execute(
                "INSERT INTO chat_messages (user_id, body, created_at) "
                "VALUES (?, ?, ?)", (frank["id"], body, _now_iso()))
            conn.commit()
            row = conn.execute(
                _CHAT_SELECT + "WHERE m.id = ?",
                (cur.lastrowid,)).fetchone()
        view = _chat_view(row)
        view["reactions"] = {"counts": {}, "by": {}, "mine": []}
        _hub.broadcast({"type": "message", "message": view})
    except sqlite3.OperationalError:
        pass


_FRANK_NEWS_NOUNS = {
    "halloween": "haunt", "events": "event",
    "halloween_stores": "Halloween store", "live": "live room",
    "restaurants": "restaurhaunt", "coffee": "spooky coffee spot",
    "shops": "shop", "parks": "haunted park", "hotels": "hotel",
    "ice_cream": "ice cream shop",
    "haunted_houses": "haunted house", "christmas": "holiday display",
}


def _frank_announce_new_listing(entry_id: int) -> None:
    """Frank announces the site (brief §4): a new listing posted
    through /upload gets a shout in the chat room — '📣 New haunt:
    <title> (<town>) /d/<id>'. THROTTLED so a bulk-posting session
    can't flood the room: at most one shout per
    FRANK_NEWS_MIN_GAP_S and FRANK_NEWS_HOURLY_CAP per hour; listings
    that arrive inside a closed window accumulate, and the next shout
    batches them ('N new listings… the newest: …'). System-only —
    fired from the upload path, never user-triggerable — and
    best-effort: an announcement failure never fails an upload."""
    try:
        now = datetime.now(timezone.utc)
        with get_conn(DB_PATH) as conn:
            row = conn.execute(
                "SELECT title, town, category FROM entries WHERE id = ?",
                (entry_id,)).fetchone()
        if row is None:
            return
        try:
            pending = int(_social_meta_get(FRANK_NEWS_PENDING_KEY) or 0)
        except (TypeError, ValueError):
            pending = 0
        hour_key = now.strftime("%Y-%m-%dT%H")
        hour_raw = _social_meta_get(FRANK_NEWS_HOUR_KEY) or ""
        hour_count = 0
        if hour_raw.startswith(hour_key + ":"):
            try:
                hour_count = int(hour_raw.split(":", 1)[1])
            except (TypeError, ValueError):
                hour_count = 0
        last_raw = _social_meta_get(FRANK_NEWS_LAST_KEY)
        last_ts = None
        if last_raw:
            try:
                last_ts = datetime.fromisoformat(last_raw)
            except ValueError:
                last_ts = None
        gap_ok = (last_ts is None or (now - last_ts).total_seconds()
                  >= FRANK_NEWS_MIN_GAP_S)
        if not gap_ok or hour_count >= FRANK_NEWS_HOURLY_CAP:
            _social_meta_set(FRANK_NEWS_PENDING_KEY, str(pending + 1))
            return
        noun = _FRANK_NEWS_NOUNS.get(row["category"], "listing")
        town = (row["town"] or "").strip()
        where = f" ({town})" if town else ""
        if pending > 0:
            total = pending + 1
            body = (f"📣 {total} new listings just landed on HauntMap — "
                    f"the newest: {row['title']}{where} — take a peek! "
                    f"/d/{entry_id}")
        else:
            body = (f"📣 New {noun} just landed: {row['title']}{where} "
                    f"— take a peek! /d/{entry_id}")
        _social_meta_set(FRANK_NEWS_PENDING_KEY, "0")
        _social_meta_set(FRANK_NEWS_LAST_KEY, now.isoformat())
        _social_meta_set(FRANK_NEWS_HOUR_KEY,
                         f"{hour_key}:{hour_count + 1}")
        _frank_announce(body)
        # Wave 1 web push: Frank's site announcements also reach
        # opted-in members who aren't in the room (kind 'frank').
        # The throttle above (1 per 10 min, 6 per hour) is this
        # fan-out's rate limit too. Best-effort, like the shout.
        push_mod.notify_frank_fans(
            DB_PATH, "📣 New on HauntMap",
            re.sub(r"\s*/d/\d+\s*$", "", body), f"/d/{entry_id}",
            online_ids=set(_hub.conns))
    except Exception:
        pass


def _game_players(conn, g: dict) -> dict:
    """{user_id: {"handle", "avatar"}} for a game's two players."""
    out = {}
    for uid in (g["challenger_id"], g["opponent_id"]):
        row = conn.execute(
            "SELECT u.handle, p.display_name, p.avatar_choice, "
            "p.avatar_path FROM users u "
            "LEFT JOIN profiles p ON p.user_id = u.id WHERE u.id = ?",
            (uid,)).fetchone()
        if row:
            out[uid] = {
                "handle": row["handle"],
                "avatar": _avatar_view(row["avatar_choice"],
                                       row["display_name"],
                                       row["handle"], row["avatar_path"])}
    return out


def _game_public_state(g: dict) -> dict:
    """The state a client may see. Secrets stay server-side: Ghost
    Word's answer is masked, Unscramble's word is never sent while a
    round is open."""
    state = g["state"]
    kind = g["kind"]
    if kind == "ghost_word":
        word = state.get("word", "")
        guessed = state.get("guessed", [])
        return {"masked": " ".join(
                    ch if ch in guessed else "_" for ch in word),
                "guessed": guessed, "wrong": state.get("wrong", 0),
                "max_wrong": GHOST_MAX_WRONG, "turn": state.get("turn"),
                "word": word if g["status"] == "finished" else None}
    if kind == "unscramble":
        return {"round": state.get("round", 1), "rounds": UNSCRAMBLE_ROUNDS,
                "scrambled": state.get("scrambled", ""),
                "scores": state.get("scores", {}),
                "round_open": state.get("round_open", False),
                "round_winner": state.get("round_winner"),
                "last_word": state.get("last_word")}
    if kind == "word_chain":
        return {"current": state.get("current"),
                "used": state.get("used", [])[-14:],
                "turn": state.get("turn"),
                "strikes": state.get("strikes", {}),
                "bonus": state.get("bonus", {}),
                "deadline": state.get("deadline")}
    return {}


def _game_view(conn, g: dict, viewer_id: int | None) -> dict:
    players = _game_players(conn, g)
    c_id, o_id = g["challenger_id"], g["opponent_id"]
    winner = None
    if g.get("winner_id"):
        wrow = conn.execute("SELECT handle FROM users WHERE id = ?",
                            (g["winner_id"],)).fetchone()
        winner = wrow["handle"] if wrow else None
    state = _game_public_state(g)
    return {"id": g["id"], "kind": g["kind"],
            "label": GAME_KIND_LABELS.get(g["kind"], g["kind"]),
            "status": g["status"],
            "challenger": players.get(c_id, {}),
            "opponent": players.get(o_id, {}),
            "challenger_id": c_id, "opponent_id": o_id,
            "winner": winner,
            "state": state,
            "is_player": viewer_id in (c_id, o_id),
            "my_turn": state.get("turn") == viewer_id,
            "detail": g["state"].get("detail"),
            "expires_at": g.get("expires_at"),
            "created_at": g.get("created_at")}


def _game_row(conn, game_id: int) -> dict | None:
    row = conn.execute("SELECT * FROM chat_games WHERE id = ?",
                       (game_id,)).fetchone()
    if row is None:
        return None
    g = dict(row)
    try:
        g["state"] = json.loads(g["state"] or "{}")
    except ValueError:
        g["state"] = {}
    return g


def _game_save(conn, g: dict) -> None:
    conn.execute(
        "UPDATE chat_games SET status = ?, state = ?, winner_id = ?, "
        "updated_at = ? WHERE id = ?",
        (g["status"], json.dumps(g["state"]), g.get("winner_id"),
         _now_iso(), g["id"]))


def _game_broadcast(g: dict, viewerless: bool = False) -> None:
    with get_conn(DB_PATH) as conn:
        view = _game_view(conn, g, None)
    # Per-viewer flags (is_player/my_turn) are recomputed by clients
    # from the id fields the view carries; the broadcast payload is
    # the neutral spectator view.
    _hub.broadcast({"type": "game", "game": view})


def _tally_win_loss(conn, winner_id: int, loser_id: int,
                    kind: str) -> None:
    for uid, col in ((winner_id, "wins"), (loser_id, "losses")):
        conn.execute(
            "INSERT INTO chat_game_tallies (user_id, kind, wins, "
            "losses) VALUES (?, ?, ?, ?) "
            "ON CONFLICT(user_id, kind) DO UPDATE SET "
            "wins = wins + excluded.wins, "
            "losses = losses + excluded.losses",
            (uid, kind, 1 if col == "wins" else 0,
             1 if col == "losses" else 0))


def _finish_game(conn, g: dict, winner_id: int | None,
                 detail: str) -> dict:
    """Terminal transition: status, tally, Frank's result post, and a
    live game event. Returns the public view."""
    g["status"] = "finished"
    g["winner_id"] = winner_id
    g["state"]["detail"] = detail
    _game_save(conn, g)
    players = _game_players(conn, g)
    c_h = players.get(g["challenger_id"], {}).get("handle", "?")
    o_h = players.get(g["opponent_id"], {}).get("handle", "?")
    label = GAME_KIND_LABELS.get(g["kind"], g["kind"])
    if winner_id:
        loser_id = (g["opponent_id"] if winner_id == g["challenger_id"]
                    else g["challenger_id"])
        _tally_win_loss(conn, winner_id, loser_id, g["kind"])
        w_h = players.get(winner_id, {}).get("handle", "?")
        l_h = players.get(loser_id, {}).get("handle", "?")
        text = (f"🏆 @{w_h} beat @{l_h} at {label} — {detail} "
                f"Rematch, anyone?")
    else:
        text = (f"🏁 @{c_h} vs @{o_h} at {label} ended level — "
                f"{detail} Rematch, anyone?")
    conn.commit()
    view = _game_view(conn, g, None)
    _frank_announce(text)
    _hub.broadcast({"type": "game", "game": view})
    return view


def _scramble(word: str) -> str:
    letters = list(word)
    for _ in range(24):
        random.shuffle(letters)
        if "".join(letters) != word:
            break
    return "".join(letters)


def _game_init_state(kind: str, challenger_id: int,
                     opponent_id: int) -> dict:
    if kind == "ghost_word":
        return {"word": random.choice(_GAME_WORD_POOL), "guessed": [],
                "wrong": 0, "turn": challenger_id}
    if kind == "unscramble":
        word = random.choice(_GAME_WORD_POOL)
        return {"round": 1, "word": word, "scrambled": _scramble(word),
                "scores": {str(challenger_id): 0, str(opponent_id): 0},
                "round_open": True, "round_winner": None,
                "last_word": None, "used": [word]}
    if kind == "word_chain":
        return {"current": None, "used": [], "turn": challenger_id,
                "strikes": {str(challenger_id): 0, str(opponent_id): 0},
                "bonus": {str(challenger_id): 0, str(opponent_id): 0},
                "deadline": (datetime.now(timezone.utc)
                             + timedelta(seconds=CHAIN_TURN_S)
                             ).isoformat()}
    return {}


def _chain_apply_timeout(g: dict) -> bool:
    """Word Chain's turn timer, enforced lazily on view/move: a player
    who lets the clock run out takes a strike and loses the turn; two
    strikes ends the game. Returns True if state changed."""
    if g["kind"] != "word_chain" or g["status"] != "active":
        return False
    state = g["state"]
    now = datetime.now(timezone.utc)
    try:
        deadline = datetime.fromisoformat(state["deadline"])
    except (KeyError, ValueError):
        return False
    if now <= deadline:
        return False
    turn = state["turn"]
    other = (g["opponent_id"] if turn == g["challenger_id"]
             else g["challenger_id"])
    state["strikes"][str(turn)] = state["strikes"].get(str(turn), 0) + 1
    if state["strikes"][str(turn)] >= CHAIN_MAX_STRIKES:
        g["_timeout_finish"] = other
        return True
    state["turn"] = other
    state["deadline"] = (now + timedelta(seconds=CHAIN_TURN_S)).isoformat()
    return True


def _expire_challenges(conn) -> None:
    conn.execute(
        "UPDATE chat_games SET status = 'expired', updated_at = ? "
        "WHERE status = 'pending' AND expires_at IS NOT NULL "
        "AND expires_at < ?", (_now_iso(), _now_iso()))
    conn.commit()


def _chat_games_for_room(member: dict) -> list[dict]:
    """Games the room renders: live challenges + active games (open to
    spectators) + just-finished ones (result card + Rematch), newest
    first. Pending invites older than their window are expired here."""
    views = []
    with get_conn(DB_PATH) as conn:
        _expire_challenges(conn)
        rows = conn.execute(
            "SELECT * FROM chat_games WHERE status IN ('pending', "
            "'active') OR (status = 'finished' AND updated_at > ?) "
            "ORDER BY id DESC LIMIT 14",
            ((datetime.now(timezone.utc)
              - timedelta(minutes=15)).isoformat(),)).fetchall()
        games = []
        for row in rows:
            g = dict(row)
            try:
                g["state"] = json.loads(g["state"] or "{}")
            except ValueError:
                g["state"] = {}
            if _chain_apply_timeout(g):
                if g.get("_timeout_finish"):
                    _finish_game(conn, g, g.pop("_timeout_finish"),
                                 "ran out of time twice in the chain.")
                else:
                    _game_save(conn, g)
                    conn.commit()
            games.append(g)
        views = [_game_view(conn, g, member["id"]) for g in games]
    return views


@app.get("/api/chat/games")
def chat_games(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    return JSONResponse({"games": _chat_games_for_room(member)})


@app.post("/api/chat/challenge")
async def chat_challenge(request: Request):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    try:
        data = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    kind = str(data.get("kind") or "")
    if kind not in GAME_KIND_LABELS:
        return JSONResponse({"ok": False, "error": "unknown game"},
                            status_code=400)
    handle = str(data.get("handle") or "").strip().lower().lstrip("@")
    if handle == member["handle"]:
        return JSONResponse(
            {"ok": False, "error": "You can't challenge yourself."},
            status_code=400)
    now = datetime.now(timezone.utc)
    with get_conn(DB_PATH) as conn:
        target = conn.execute(
            "SELECT u.id, u.handle, p.no_challenges FROM users u "
            "LEFT JOIN profiles p ON p.user_id = u.id "
            "WHERE u.handle = ? AND u.status = 'active'",
            (handle,)).fetchone()
        if target is None:
            return JSONResponse({"ok": False,
                                 "error": "No such member."},
                                status_code=404)
        if target["no_challenges"]:
            return JSONResponse(
                {"ok": False,
                 "error": f"@{handle} has game challenges turned off."},
                status_code=403)
        blocked = conn.execute(
            "SELECT 1 FROM blocks WHERE (blocker_id = ? AND "
            "blocked_id = ?) OR (blocker_id = ? AND blocked_id = ?)",
            (member["id"], target["id"], target["id"],
             member["id"])).fetchone()
        if blocked:
            return JSONResponse(
                {"ok": False, "error": "You can't challenge that member."},
                status_code=403)
        if (member["id"], target["id"]) in _DECLINE_MUTES:
            return JSONResponse(
                {"ok": False,
                 "error": f"@{handle} passed on your last challenge — "
                          "give it a rest for now."}, status_code=403)
        _expire_challenges(conn)
        outgoing = conn.execute(
            "SELECT 1 FROM chat_games WHERE challenger_id = ? "
            "AND status = 'pending'", (member["id"],)).fetchone()
        if outgoing:
            return JSONResponse(
                {"ok": False,
                 "error": "You already have a challenge out — wait for "
                          "an answer first."}, status_code=409)
        recent = conn.execute(
            "SELECT COUNT(*) AS n FROM chat_games WHERE challenger_id "
            "= ? AND created_at > ?",
            (member["id"],
             (now - timedelta(hours=1)).isoformat())).fetchone()["n"]
        if recent >= CHAT_CHALLENGE_HOURLY_CAP:
            return JSONResponse(
                {"ok": False,
                 "error": "That's a lot of challenges — take a breather."},
                status_code=429)
        cur = conn.execute(
            "INSERT INTO chat_games (kind, challenger_id, opponent_id, "
            "status, state, created_at, updated_at, expires_at) "
            "VALUES (?, ?, ?, 'pending', '{}', ?, ?, ?)",
            (kind, member["id"], target["id"], now.isoformat(),
             now.isoformat(),
             (now + timedelta(seconds=CHAT_CHALLENGE_TTL_S)).isoformat()))
        conn.commit()
        g = _game_row(conn, cur.lastrowid)
        view = _game_view(conn, g, member["id"])
        challenger_muted = member["id"] in _shadow_muted_ids(conn)
    _hub.broadcast({"type": "game", "game": view})
    _frank_announce(
        f"⚔️ @{member['handle']} challenged @{handle} to "
        f"{GAME_KIND_LABELS[kind]}! Will they accept?")
    # Wave 1 web push: call the challenged member back if they're
    # away. Blocks and the challenges opt-out were enforced above
    # (this code only runs on a created challenge); a shadow-muted
    # challenger's invite never pushes.
    if not challenger_muted:
        push_mod.notify_user(
            DB_PATH, target["id"], "challenges",
            "⚔️ You've been challenged in Haunt Chat!",
            f"@{member['handle']} challenged you to "
            f"{GAME_KIND_LABELS[kind]} — it expires in two minutes!",
            url="/chat", ref=f"from-{member['id']}",
            online_ids=set(_hub.conns))
    return JSONResponse({"ok": True, "game": view})


@app.post("/api/chat/games/{game_id}/accept")
def chat_game_accept(request: Request, game_id: int):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    with get_conn(DB_PATH) as conn:
        g = _game_row(conn, game_id)
        if g is None or g["opponent_id"] != member["id"]:
            return JSONResponse({"ok": False, "error": "not your game"},
                                status_code=404)
        if g["status"] != "pending":
            return JSONResponse({"ok": False,
                                 "error": "That challenge is over."},
                                status_code=409)
        if g["expires_at"] and g["expires_at"] < _now_iso():
            g["status"] = "expired"
            _game_save(conn, g)
            conn.commit()
            return JSONResponse({"ok": False,
                                 "error": "That challenge expired."},
                                status_code=409)
        g["state"] = _game_init_state(g["kind"], g["challenger_id"],
                                      g["opponent_id"])
        g["status"] = "active"
        g["expires_at"] = None
        _game_save(conn, g)
        conn.commit()
        view = _game_view(conn, g, member["id"])
    _hub.broadcast({"type": "game", "game": view})
    return JSONResponse({"ok": True, "game": view})


@app.post("/api/chat/games/{game_id}/decline")
def chat_game_decline(request: Request, game_id: int):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    with get_conn(DB_PATH) as conn:
        g = _game_row(conn, game_id)
        if g is None or g["opponent_id"] != member["id"]:
            return JSONResponse({"ok": False, "error": "not your game"},
                                status_code=404)
        if g["status"] != "pending":
            return JSONResponse({"ok": False,
                                 "error": "That challenge is over."},
                                status_code=409)
        g["status"] = "declined"
        _game_save(conn, g)
        conn.commit()
        view = _game_view(conn, g, member["id"])
    # Declining is silent (brief §7.1): no announcement, and the pair's
    # invites mute for the session so it can't become harassment.
    _DECLINE_MUTES.add((g["challenger_id"], g["opponent_id"]))
    _hub.broadcast({"type": "game", "game": view})
    return JSONResponse({"ok": True, "game": view})


@app.post("/api/chat/games/{game_id}/cancel")
def chat_game_cancel(request: Request, game_id: int):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    with get_conn(DB_PATH) as conn:
        g = _game_row(conn, game_id)
        if g is None or g["challenger_id"] != member["id"]:
            return JSONResponse({"ok": False, "error": "not your game"},
                                status_code=404)
        if g["status"] != "pending":
            return JSONResponse({"ok": False,
                                 "error": "That challenge is already live."},
                                status_code=409)
        g["status"] = "cancelled"
        _game_save(conn, g)
        conn.commit()
        view = _game_view(conn, g, member["id"])
    _hub.broadcast({"type": "game", "game": view})
    return JSONResponse({"ok": True, "game": view})


@app.post("/api/chat/games/{game_id}/rematch")
def chat_game_rematch(request: Request, game_id: int):
    """One tap on a finished game's card: a fresh game, same pairing
    and kind, live immediately (both players already consented by
    playing the first one)."""
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    now = datetime.now(timezone.utc)
    with get_conn(DB_PATH) as conn:
        old = _game_row(conn, game_id)
        if old is None or member["id"] not in (old["challenger_id"],
                                               old["opponent_id"]):
            return JSONResponse({"ok": False, "error": "not your game"},
                                status_code=404)
        if old["status"] != "finished":
            return JSONResponse({"ok": False,
                                 "error": "That game isn't over yet."},
                                status_code=409)
        other_id = (old["opponent_id"] if member["id"] == old["challenger_id"]
                    else old["challenger_id"])
        state = _game_init_state(old["kind"], member["id"], other_id)
        cur = conn.execute(
            "INSERT INTO chat_games (kind, challenger_id, opponent_id, "
            "status, state, created_at, updated_at) "
            "VALUES (?, ?, ?, 'active', ?, ?, ?)",
            (old["kind"], member["id"], other_id, json.dumps(state),
             now.isoformat(), now.isoformat()))
        conn.commit()
        g = _game_row(conn, cur.lastrowid)
        view = _game_view(conn, g, member["id"])
        other = conn.execute("SELECT handle FROM users WHERE id = ?",
                             (other_id,)).fetchone()
    _hub.broadcast({"type": "game", "game": view})
    _frank_announce(
        f"🔁 Rematch! @{member['handle']} runs it back against "
        f"@{other['handle'] if other else '?'} at "
        f"{GAME_KIND_LABELS[old['kind']]}.")
    return JSONResponse({"ok": True, "game": view})


@app.post("/api/chat/games/{game_id}/move")
async def chat_game_move(request: Request, game_id: int):
    member = current_member(request)
    if not member:
        return JSONResponse({"error": "members only"}, status_code=401)
    try:
        data = await request.json()
    except Exception:
        return JSONResponse({"ok": False, "error": "bad request"},
                            status_code=400)
    me = member["id"]
    with get_conn(DB_PATH) as conn:
        g = _game_row(conn, game_id)
        if g is None or me not in (g["challenger_id"], g["opponent_id"]):
            return JSONResponse({"ok": False, "error": "not your game"},
                                status_code=404)
        if g["status"] != "active":
            return JSONResponse({"ok": False,
                                 "error": "That game isn't live."},
                                status_code=409)
        other = (g["opponent_id"] if me == g["challenger_id"]
                 else g["challenger_id"])
        state = g["state"]
        err = None
        if g["kind"] == "word_chain" and _chain_apply_timeout(g):
            if g.get("_timeout_finish"):
                view = _finish_game(conn, g, g.pop("_timeout_finish"),
                                    "ran out of time twice in the chain.")
                return JSONResponse({"ok": True, "game": view})
            _game_save(conn, g)
            conn.commit()
            _hub.broadcast({"type": "game", "game": _game_view(conn, g, None)})
            state = g["state"]

        if g["kind"] == "ghost_word":
            if state["turn"] != me:
                err = "Not your turn."
            else:
                letter = str(data.get("letter") or "").strip().lower()
                if len(letter) != 1 or not letter.isalpha():
                    err = "Guess one letter."
                elif letter in state["guessed"]:
                    err = "Already guessed that one."
                else:
                    state["guessed"].append(letter)
                    word = state["word"]
                    if letter not in word:
                        state["wrong"] += 1
                    if all(ch in state["guessed"] for ch in word):
                        view = _finish_game(
                            conn, g, me,
                            f"got '{word}' with {state['wrong']} wrong "
                            f"guess{'es' if state['wrong'] != 1 else ''}.")
                        return JSONResponse({"ok": True, "game": view})
                    if state["wrong"] >= GHOST_MAX_WRONG:
                        view = _finish_game(
                            conn, g, other,
                            f"the ghost got fully built — '{word}' "
                            f"stayed hidden.")
                        return JSONResponse({"ok": True, "game": view})
                    state["turn"] = other
        elif g["kind"] == "unscramble":
            if data.get("action") == "next":
                if state["round_open"]:
                    err = "This round is still open."
                elif state["round"] >= UNSCRAMBLE_ROUNDS:
                    err = "That was the last round."
                else:
                    used = state.get("used", [])
                    pool = [w for w in _GAME_WORD_POOL if w not in used]
                    word = random.choice(pool or _GAME_WORD_POOL)
                    state["round"] += 1
                    state["word"] = word
                    state["scrambled"] = _scramble(word)
                    state["round_open"] = True
                    state["round_winner"] = None
                    state["used"] = used + [word]
            else:
                guess = str(data.get("guess") or "").strip().lower()
                if not state["round_open"]:
                    err = "That round is decided — start the next one."
                elif not guess:
                    err = "Type your unscrambled guess."
                elif guess == state["word"]:
                    state["scores"][str(me)] = \
                        state["scores"].get(str(me), 0) + 1
                    state["round_open"] = False
                    state["round_winner"] = me
                    state["last_word"] = state["word"]
                    if state["round"] >= UNSCRAMBLE_ROUNDS:
                        c_score = state["scores"].get(
                            str(g["challenger_id"]), 0)
                        o_score = state["scores"].get(
                            str(g["opponent_id"]), 0)
                        winner = (g["challenger_id"] if c_score > o_score
                                  else g["opponent_id"] if o_score > c_score
                                  else None)
                        view = _finish_game(
                            conn, g, winner,
                            f"final score {c_score}–{o_score} "
                            f"in the Unscramble.")
                        return JSONResponse({"ok": True, "game": view})
                else:
                    _game_save(conn, g)
                    conn.commit()
                    view = _game_view(conn, g, me)
                    return JSONResponse({"ok": True, "correct": False,
                                         "game": view})
        elif g["kind"] == "word_chain":
            if state["turn"] != me:
                err = "Not your turn."
            else:
                word = str(data.get("word") or "").strip().lower()
                current = state.get("current")
                if len(word) < 3 or not word.isalpha():
                    err = "Words are 3+ letters, letters only."
                elif current and word[0] != current[-1]:
                    err = f"Your word must start with '{current[-1]}'."
                elif word in state["used"]:
                    err = "That word is already used in this chain."
                elif word not in _wordlist_set():
                    err = "That one's not in the dictionary."
                elif _chat_filter_hit(word):
                    err = "Let's keep it family-friendly."
                else:
                    state["used"].append(word)
                    state["current"] = word
                    if word in _HALLOWEEN_SET:
                        state["bonus"][str(me)] = \
                            state["bonus"].get(str(me), 0) + 1
                    state["turn"] = other
                    state["deadline"] = (
                        datetime.now(timezone.utc)
                        + timedelta(seconds=CHAIN_TURN_S)).isoformat()
        if err:
            return JSONResponse({"ok": False, "error": err},
                                status_code=400)
        _game_save(conn, g)
        conn.commit()
        view = _game_view(conn, g, me)
        bview = _game_view(conn, g, None)
    _hub.broadcast({"type": "game", "game": bview})
    return JSONResponse({"ok": True, "game": view})


# ------------------------------------------------------------------- profiles

def _profile_context(request: Request, handle: str, member: dict | None,
                     wall_error: str | None = None) -> dict | None:
    """Everything profile.html needs, or None when the handle is unknown."""
    with get_conn(DB_PATH) as conn:
        urow = conn.execute("SELECT * FROM users WHERE handle = ?",
                            (handle,)).fetchone()
        if urow is None:
            return None
        user = dict(urow)
        prow = conn.execute("SELECT * FROM profiles WHERE user_id = ?",
                            (user["id"],)).fetchone()
        profile = dict(prow) if prow else {"user_id": user["id"],
                                           "display_name": user["handle"],
                                           "bio": None, "town": None,
                                           "avatar_choice": None,
                                           "banner_choice": None,
                                           "music_embed_url": None,
                                           "website_url": None}
        haunts = [row_to_dict(r) for r in conn.execute(
            "SELECT * FROM entries WHERE owner_user_id = ? AND hidden = 0 "
            "ORDER BY created_at DESC", (user["id"],)).fetchall()]
        # My Top 8 (things, not people): haunt slots join their pin so
        # the card renders live data; a hidden/deleted pin drops out.
        top8 = []
        for r in conn.execute(
                "SELECT t.slot, t.kind, t.film_title, e.id AS entry_id, "
                "e.title AS entry_title, e.town AS entry_town, "
                "e.thumb_path AS entry_thumb, e.media_path AS entry_media "
                "FROM profile_top8 t "
                "LEFT JOIN entries e ON e.id = t.entry_id AND e.hidden = 0 "
                "WHERE t.user_id = ? ORDER BY t.slot",
                (user["id"],)).fetchall():
            item = dict(r)
            if item["kind"] == "haunt" and item["entry_id"]:
                item["thumb_url"] = (
                    f"/media/{item['entry_thumb']}" if item["entry_thumb"]
                    else (f"/media/{item['entry_media']}"
                          if item["entry_media"] else ""))
                top8.append(item)
            elif item["kind"] == "film" and item["film_title"]:
                top8.append(item)
        comments = []
        for r in conn.execute(
                "SELECT w.*, a.handle AS author_handle, "
                "p.display_name AS author_name, p.avatar_choice AS author_avatar, "
                "p.avatar_path AS author_avatar_path "
                "FROM wall_comments w JOIN users a ON a.id = w.author_user_id "
                "LEFT JOIN profiles p ON p.user_id = a.id "
                "WHERE w.profile_user_id = ? AND w.hidden = 0 "
                "ORDER BY w.created_at ASC", (user["id"],)).fetchall():
            c = dict(r)
            c["author_avatar_view"] = _avatar_view(
                c.get("author_avatar"), c.get("author_name"), c["author_handle"],
                c.get("author_avatar_path"))
            c["author_label"] = c.get("author_name") or c["author_handle"]
            comments.append(c)
        photos = [dict(r) for r in conn.execute(
            "SELECT id, path, thumb_path FROM profile_photos "
            "WHERE user_id = ? ORDER BY id ASC", (user["id"],)).fetchall()]
        # Haunt Passport block (#11): the profile OWNER's synced
        # stamps — public social proof, whoever is viewing.
        passport_block = _passport_stamps_view(conn, user["id"])
        viewer_blocked = viewer_is_blocked = False
        if member and member["id"] != user["id"]:
            viewer_blocked = conn.execute(
                "SELECT 1 FROM blocks WHERE blocker_id = ? AND blocked_id = ?",
                (member["id"], user["id"])).fetchone() is not None
            viewer_is_blocked = conn.execute(
                "SELECT 1 FROM blocks WHERE blocker_id = ? AND blocked_id = ?",
                (user["id"], member["id"])).fetchone() is not None
        # Chat-game record (Oct 27): W/L per game kind from the tallies
        # table; empty until the member has finished a game.
        try:
            game_record = [
                {"kind": r["kind"], "wins": r["wins"], "losses": r["losses"]}
                for r in conn.execute(
                    "SELECT kind, wins, losses FROM chat_game_tallies "
                    "WHERE user_id = ? AND (wins + losses) > 0",
                    (user["id"],)).fetchall()]
        except sqlite3.OperationalError:
            game_record = []
    display = profile.get("display_name") or user["handle"]
    embed = _music_embed(profile.get("music_embed_url"))
    gtk = _gtk_view(profile, bool(embed),
                    haunts[0]["id"] if haunts else None)
    banner = BANNER_PRESETS.get(profile.get("banner_choice") or "",
                                 BANNER_PRESETS[DEFAULT_BANNER])
    if profile.get("banner_choice") == FRANK_BANNER_CHOICE:
        # The host's banner is the site's Frank header art under a scrim.
        banner = ("linear-gradient(rgba(13,10,24,.22), rgba(13,10,24,.68)), "
                  f"url('{FRANK_ART}') center 28%/cover")
    return {
        "request": request,
        "member": member,
        "user": user,
        "profile": profile,
        "display_name": display,
        "avatar": _avatar_view(profile.get("avatar_choice"), display, user["handle"],
                               profile.get("avatar_path")),
        "banner_gradient": banner,
        "theme": _theme_view(profile.get("theme")),
        "top8": top8,
        "treat_stickers": TREAT_STICKERS,
        "member_since": _member_since_label(user["created_at"]),
        "embed": embed,
        "gtk": gtk,
        "passport": passport_block,
        "photos": photos,
        "haunts": haunts,
        "comments": comments,
        "is_owner": bool(member and member["id"] == user["id"]),
        "viewer_blocked": viewer_blocked,
        "viewer_is_blocked": viewer_is_blocked,
        "wall_error": wall_error,
        "game_record": game_record,
        "reported": request.query_params.get("reported") == "1",
        "not_found": False,
    }


@app.get("/@{handle}", response_class=HTMLResponse)
def profile_page(request: Request, handle: str):
    handle_n = handle.strip().lower()
    if handle_n != handle:
        return RedirectResponse(f"/@{handle_n}", status_code=302)
    member = current_member(request)
    ctx = _profile_context(request, handle_n, member)
    if ctx is None:
        return templates.TemplateResponse(
            request, "profile.html",
            {"request": request, "not_found": True, "member": member,
             "handle": handle_n}, status_code=404)
    return templates.TemplateResponse(request, "profile.html", ctx)


@app.post("/@{handle}/wall", response_class=HTMLResponse)
def wall_post(request: Request, handle: str, text: str = Form(""),
              sticker: str = Form("")):
    handle_n = handle.strip().lower()
    member = current_member(request)
    if not member:
        return RedirectResponse(f"/login?next=/@{handle_n}", status_code=303)

    def fail(msg: str):
        ctx = _profile_context(request, handle_n, member, wall_error=msg)
        if ctx is None:
            raise HTTPException(404, "No such profile.")
        return templates.TemplateResponse(request, "profile.html", ctx,
                                          status_code=400)

    with get_conn(DB_PATH) as conn:
        owner = conn.execute("SELECT * FROM users WHERE handle = ?",
                             (handle_n,)).fetchone()
        if owner is None:
            raise HTTPException(404, "No such profile.")
        blocked = conn.execute(
            "SELECT 1 FROM blocks WHERE (blocker_id = ? AND blocked_id = ?) "
            "OR (blocker_id = ? AND blocked_id = ?)",
            (owner["id"], member["id"], member["id"], owner["id"])).fetchone()
        recent = conn.execute(
            "SELECT COUNT(*) AS n FROM wall_comments WHERE author_user_id = ? "
            "AND created_at > ?",
            (member["id"], (datetime.now(timezone.utc)
                             - timedelta(hours=1)).isoformat())).fetchone()["n"]
    body = text.strip()
    # One treat sticker per comment, from the fixed set only.
    treat = sticker if sticker in TREAT_STICKERS else None
    if blocked:
        return fail("You can't comment on this profile.")
    if not body:
        return fail("Write something first.")
    if len(body) > 500:
        return fail("Comments cap at 500 characters.")
    if recent >= 10:
        return fail("Whoa — 10 comments an hour is the cap. Take a breather.")
    if _account_age_days(member) < 7 and _contains_link(body):
        return fail("New accounts can't post links in comments for the "
                    "first 7 days — them's the anti-spam rules.")
    with get_conn(DB_PATH) as conn:
        conn.execute(
            "INSERT INTO wall_comments (profile_user_id, author_user_id, text, "
            "sticker, created_at) VALUES (?, ?, ?, ?, ?)",
            (owner["id"], member["id"], body, treat,
             datetime.now(timezone.utc).isoformat()))
        conn.commit()
    return RedirectResponse(f"/@{handle_n}", status_code=303)


@app.post("/@{handle}/report")
def profile_report(request: Request, handle: str, reason: str = Form("")):
    member = current_member(request)
    handle_n = handle.strip().lower()
    if not member:
        return RedirectResponse(f"/login?next=/@{handle_n}", status_code=303)
    with get_conn(DB_PATH) as conn:
        owner = conn.execute("SELECT id FROM users WHERE handle = ?",
                             (handle_n,)).fetchone()
        if owner:
            conn.execute(
                "INSERT INTO reports (reporter_user_id, target_type, target_id, "
                "reason, created_at) VALUES (?, 'profile', ?, ?, ?)",
                (member["id"], owner["id"], reason.strip()[:500] or None,
                 datetime.now(timezone.utc).isoformat()))
            conn.commit()
    return RedirectResponse(f"/@{handle_n}?reported=1", status_code=303)


@app.post("/@{handle}/block")
def profile_block(request: Request, handle: str):
    member = current_member(request)
    handle_n = handle.strip().lower()
    if not member:
        return RedirectResponse(f"/login?next=/@{handle_n}", status_code=303)
    with get_conn(DB_PATH) as conn:
        owner = conn.execute("SELECT id FROM users WHERE handle = ?",
                             (handle_n,)).fetchone()
        if owner and owner["id"] != member["id"]:
            conn.execute(
                "INSERT OR IGNORE INTO blocks (blocker_id, blocked_id, created_at) "
                "VALUES (?, ?, ?)",
                (member["id"], owner["id"], datetime.now(timezone.utc).isoformat()))
            conn.commit()
    return RedirectResponse(f"/@{handle_n}", status_code=303)


@app.post("/@{handle}/unblock")
def profile_unblock(request: Request, handle: str):
    member = current_member(request)
    handle_n = handle.strip().lower()
    if not member:
        return RedirectResponse(f"/login?next=/@{handle_n}", status_code=303)
    with get_conn(DB_PATH) as conn:
        owner = conn.execute("SELECT id FROM users WHERE handle = ?",
                             (handle_n,)).fetchone()
        if owner:
            conn.execute(
                "DELETE FROM blocks WHERE blocker_id = ? AND blocked_id = ?",
                (member["id"], owner["id"]))
            conn.commit()
    return RedirectResponse(f"/@{handle_n}", status_code=303)


@app.post("/wall/{comment_id}/delete")
def wall_delete(request: Request, comment_id: int):
    member = current_member(request)
    if not member:
        return RedirectResponse("/login", status_code=303)
    with get_conn(DB_PATH) as conn:
        row = conn.execute("SELECT * FROM wall_comments WHERE id = ?",
                           (comment_id,)).fetchone()
        if row is None:
            raise HTTPException(404, "No such comment.")
        # The wall's owner controls their wall; the author can retract too.
        if member["id"] not in (row["profile_user_id"], row["author_user_id"]):
            raise HTTPException(403, "Not your wall.")
        conn.execute("UPDATE wall_comments SET hidden = 1 WHERE id = ?",
                     (comment_id,))
        conn.commit()
        owner = conn.execute("SELECT handle FROM users WHERE id = ?",
                             (row["profile_user_id"],)).fetchone()
    return RedirectResponse(f"/@{owner['handle']}", status_code=303)


@app.post("/wall/{comment_id}/report")
def wall_report(request: Request, comment_id: int, reason: str = Form("")):
    member = current_member(request)
    if not member:
        return RedirectResponse("/login", status_code=303)
    with get_conn(DB_PATH) as conn:
        row = conn.execute("SELECT * FROM wall_comments WHERE id = ?",
                           (comment_id,)).fetchone()
        if row is None:
            raise HTTPException(404, "No such comment.")
        conn.execute(
            "INSERT INTO reports (reporter_user_id, target_type, target_id, "
            "reason, created_at) VALUES (?, 'comment', ?, ?, ?)",
            (member["id"], comment_id, reason.strip()[:500] or None,
             datetime.now(timezone.utc).isoformat()))
        conn.commit()
        owner = conn.execute("SELECT handle FROM users WHERE id = ?",
                             (row["profile_user_id"],)).fetchone()
    return RedirectResponse(f"/@{owner['handle']}?reported=1", status_code=303)


# --------------------------------------------------------------- edit profile

def _top8_edit_slots(user_id: int) -> list[dict]:
    """The 8 Top-8 slots as the edit form needs them (saved values only;
    a slot is {'slot', 'kind', 'entry_id', 'entry_label', 'film_title'})."""
    slots = [{"slot": i, "kind": "", "entry_id": None,
              "entry_label": "", "film_title": ""} for i in range(1, 9)]
    with get_conn(DB_PATH) as conn:
        for r in conn.execute(
                "SELECT t.slot, t.kind, t.entry_id, t.film_title, "
                "e.title AS entry_title, e.town AS entry_town "
                "FROM profile_top8 t "
                "LEFT JOIN entries e ON e.id = t.entry_id "
                "WHERE t.user_id = ? ORDER BY t.slot", (user_id,)).fetchall():
            s = slots[r["slot"] - 1]
            s["kind"] = r["kind"]
            if r["kind"] == "haunt" and r["entry_id"]:
                s["entry_id"] = r["entry_id"]
                s["entry_label"] = (f"{r['entry_title']} — {r['entry_town']}"
                                    if r["entry_title"] else "")
            elif r["kind"] == "film":
                s["film_title"] = r["film_title"] or ""
    return slots


def _edit_context(request: Request, member: dict, profile: dict,
                  error: str | None) -> dict:
    with get_conn(DB_PATH) as conn:
        photos = [dict(r) for r in conn.execute(
            "SELECT id, path, thumb_path FROM profile_photos "
            "WHERE user_id = ? ORDER BY id ASC", (member["id"],)).fetchall()]
    return {"request": request, "member": member, "profile": profile,
            "avatars": AVATAR_PRESETS, "banners": BANNER_PRESETS,
            "themes": PROFILE_THEMES, "default_theme": DEFAULT_THEME,
            "top8_slots": _top8_edit_slots(member["id"]),
            "films": _film_catalog_titles(),
            "photos": photos, "photo_max": PROFILE_PHOTO_MAX,
            "gtk_costume_picks": GTK_COSTUME_PICKS,
            "gtk_scare_meta": GTK_SCARE_META,
            "gtk_haunter_kinds": GTK_HAUNTER_KINDS,
            "gtk_monsters": GTK_MONSTERS,
            "gtk_season_picks": GTK_SEASON_PICKS,
            "error": error}


@app.get("/profile/edit", response_class=HTMLResponse)
def profile_edit_form(request: Request):
    member = current_member(request)
    if not member:
        return RedirectResponse("/login?next=/profile/edit", status_code=303)
    with get_conn(DB_PATH) as conn:
        prow = conn.execute("SELECT * FROM profiles WHERE user_id = ?",
                            (member["id"],)).fetchone()
    return templates.TemplateResponse(
        request, "profile_edit.html",
        _edit_context(request, member, dict(prow) if prow else {}, None))


@app.get("/api/pins/search")
def pin_search(request: Request, q: str = ""):
    """Live-pin search for the Top 8 picker. Members only — it's an
    editing tool, not a public API."""
    member = current_member(request)
    if not member:
        raise HTTPException(401, "Sign in first.")
    q = q.strip()
    if len(q) < 2:
        return JSONResponse([])
    like = f"%{q}%"
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT id, title, town FROM entries WHERE hidden = 0 "
            "AND (title LIKE ? OR town LIKE ?) "
            "ORDER BY votes DESC, id DESC LIMIT 8", (like, like)).fetchall()
    return JSONResponse([{"id": r["id"], "title": r["title"],
                          "town": r["town"]} for r in rows])


@app.post("/profile/edit", response_class=HTMLResponse)
async def profile_edit_submit(request: Request,
                              display_name: str = Form(""), bio: str = Form(""),
                              town: str = Form(""), current_city: str = Form(""),
                              avatar_choice: str = Form(""),
                              banner_choice: str = Form(""), theme: str = Form(""),
                              music_embed_url: str = Form(""),
                              fav_joke: str = Form(""),
                              costume_pick: str = Form(""),
                              costume_as: str = Form(""),
                              best_memory: str = Form(""),
                              scare_tolerance: str = Form(""),
                              haunter_kind: str = Form(""),
                              candy_fav: str = Form(""),
                              candy_trade: str = Form(""),
                              first_horror: str = Form(""),
                              monster_ego: str = Form(""),
                              haunt_name: str = Form(""),
                              haunt_theme: str = Form(""),
                              season_start: str = Form(""),
                              fav_song: str = Form(""),
                              no_challenges: str = Form("")):
    member = current_member(request)
    if not member:
        return RedirectResponse("/login?next=/profile/edit", status_code=303)
    values = {"display_name": display_name.strip(), "bio": bio.strip(),
              "town": town.strip(), "current_city": current_city.strip(),
              "avatar_choice": avatar_choice,
              "banner_choice": banner_choice, "theme": theme,
              "music_embed_url": music_embed_url.strip(),
              "fav_joke": fav_joke.strip(),
              "costume_pick": costume_pick, "costume_as": costume_as.strip(),
              "best_memory": best_memory.strip(),
              "scare_tolerance": scare_tolerance,
              "haunter_kind": haunter_kind,
              "candy_fav": candy_fav.strip(),
              "candy_trade": candy_trade.strip(),
              "first_horror": first_horror.strip(),
              "monster_ego": monster_ego,
              "haunt_name": haunt_name.strip(),
              "haunt_theme": haunt_theme.strip(),
              "season_start": season_start,
              "fav_song": fav_song.strip()}

    def fail(msg: str):
        return templates.TemplateResponse(
            request, "profile_edit.html",
            _edit_context(request, member, values, msg), status_code=400)

    if len(values["display_name"]) > 60:
        return fail("Display names cap at 60 characters.")
    if len(values["bio"]) > 500:
        return fail("Bios cap at 500 characters.")
    if len(values["town"]) > 80:
        return fail("Town caps at 80 characters.")
    if len(values["current_city"]) > 80:
        return fail("Current city caps at 80 characters.")
    if avatar_choice and avatar_choice not in AVATAR_PRESETS:
        return fail("Pick an avatar from the set.")
    if banner_choice and banner_choice not in BANNER_PRESETS:
        return fail("Pick a banner from the set.")
    if theme and theme not in PROFILE_THEMES:
        return fail("Pick a theme from the set.")
    # "Get to know me" bundle: free texts cap like town/bio do; picks
    # must come from the preset sets (or stay blank).
    gtk_cap_msgs = {
        "fav_joke": "Favorite jokes cap at 140 characters.",
        "costume_as": "Costumes cap at 80 characters.",
        "best_memory": "Best memories cap at 500 characters.",
        "candy_fav": "Favorite candy caps at 60 characters.",
        "candy_trade": "Trade-away candy caps at 60 characters.",
        "first_horror": "First horror movies cap at 120 characters.",
        "haunt_name": "Haunt names cap at 80 characters.",
        "haunt_theme": "Haunt themes cap at 80 characters.",
        "fav_song": "Favorite songs cap at 120 characters.",
    }
    for gtk_key, gtk_cap in GTK_TEXT_CAPS.items():
        if len(values[gtk_key]) > gtk_cap:
            return fail(gtk_cap_msgs[gtk_key])
    for gtk_key, gtk_set in GTK_PICK_KEYS.items():
        if values[gtk_key] and values[gtk_key] not in gtk_set:
            return fail("Pick from the set, or leave it blank.")
    music = values["music_embed_url"]
    if music and _music_embed(music) is None:
        return fail("That link can't be embedded — use a Spotify, SoundCloud, "
                    "or YouTube link.")
    # Plan §4's new-account link ban covers bio + comments. The music slot
    # is exempt by design: its URL is host-allowlisted to Spotify /
    # SoundCloud / YouTube embeds above, so it can't carry spam links.
    if _account_age_days(member) < 7 and _contains_link(values["bio"]):
        return fail("New accounts can't put links in their bio for the "
                    "first 7 days — anti-spam rules.")
    # My Top 8: 8 slots of things. Haunt slots must name a live pin;
    # film slots are catalog-or-free-text titles.
    form = await request.form()
    top8_rows = []
    for i in range(1, 9):
        kind = (form.get(f"top8_kind_{i}") or "").strip()
        if kind == "haunt":
            try:
                entry_id = int(form.get(f"top8_entry_{i}") or "")
            except ValueError:
                return fail(f"Top 8 slot {i}: search and pick a haunt "
                            "from the list.")
            with get_conn(DB_PATH) as conn:
                ok = conn.execute(
                    "SELECT 1 FROM entries WHERE id = ? AND hidden = 0",
                    (entry_id,)).fetchone()
            if not ok:
                return fail(f"Top 8 slot {i}: that haunt isn't on the "
                            "map anymore — pick another.")
            top8_rows.append((i, "haunt", entry_id, None))
        elif kind == "film":
            title = (form.get(f"top8_film_{i}") or "").strip()
            if not title:
                return fail(f"Top 8 slot {i}: name the film, or set the "
                            "slot to None.")
            if len(title) > 120:
                return fail(f"Top 8 slot {i}: film titles cap at 120 "
                            "characters.")
            top8_rows.append((i, "film", None, title))
    gtk_cols = ", ".join(GTK_COLUMNS)
    gtk_marks = ", ".join("?" for _ in GTK_COLUMNS)
    gtk_sets = ", ".join(f"{c} = excluded.{c}" for c in GTK_COLUMNS)
    gtk_params = tuple(values[c] or None for c in GTK_COLUMNS)
    with get_conn(DB_PATH) as conn:
        conn.execute(
            "INSERT INTO profiles (user_id, display_name, bio, town, "
            "current_city, avatar_choice, banner_choice, theme, "
            f"music_embed_url, {gtk_cols}, updated_at) "
            f"VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, {gtk_marks}, ?) "
            "ON CONFLICT(user_id) DO UPDATE SET display_name = excluded.display_name, "
            "bio = excluded.bio, town = excluded.town, "
            "current_city = excluded.current_city, "
            "avatar_choice = excluded.avatar_choice, "
            "banner_choice = excluded.banner_choice, "
            "theme = excluded.theme, "
            "music_embed_url = excluded.music_embed_url, "
            f"{gtk_sets}, "
            "updated_at = excluded.updated_at",
            (member["id"], values["display_name"] or member["handle"],
             values["bio"] or None, values["town"] or None,
             values["current_city"] or None,
             avatar_choice or None, banner_choice or None, theme or None,
             music or None) + gtk_params +
            (datetime.now(timezone.utc).isoformat(),))
        conn.execute("DELETE FROM profile_top8 WHERE user_id = ?",
                     (member["id"],))
        conn.executemany(
            "INSERT INTO profile_top8 (user_id, slot, kind, entry_id, "
            "film_title) VALUES (?, ?, ?, ?, ?)",
            [(member["id"], slot, kind, entry_id, film)
             for slot, kind, entry_id, film in top8_rows])
        # Game-challenge opt-out (chat games, Oct 27): a plain UPDATE so
        # the big upsert above stays untouched.
        conn.execute(
            "UPDATE profiles SET no_challenges = ? WHERE user_id = ?",
            (1 if no_challenges in ("1", "on", "true", "yes") else 0,
             member["id"]))
        conn.commit()
    return RedirectResponse(f"/@{member['handle']}", status_code=303)


# ------------------------------------------- HauntSocial photo uploads
# Dan (Oct 25): "We should be able to upload our profile picture into
# HauntSocial and add photos as well." Both flows REUSE the pin-photo
# machinery above (save_upload's size cap, PHOTO_EXTS, PIL verify,
# make_thumb's EXIF-upright + metadata-strip pipeline) and run in the
# thread pool, never on the event loop (blip hardening). An uploaded
# profile picture beats the preset avatars everywhere the avatar
# renders (see _avatar_view); profile photos cap at PROFILE_PHOTO_MAX.

PROFILE_PHOTO_MAX = 12
AVATAR_MAX_EDGE = 512


def _profile_row(user_id: int) -> dict:
    with get_conn(DB_PATH) as conn:
        prow = conn.execute("SELECT * FROM profiles WHERE user_id = ?",
                            (user_id,)).fetchone()
    return dict(prow) if prow else {}


def _edit_fail(request: Request, member: dict, msg: str):
    return templates.TemplateResponse(
        request, "profile_edit.html",
        _edit_context(request, member, _profile_row(member["id"]), msg),
        status_code=400)


def _process_avatar(tmp: Path) -> str:
    """Validate + normalize an uploaded profile picture: real image
    bytes (PIL verify), EXIF physically transposed so it displays right
    side up everywhere, metadata stripped on save, center-cropped
    square at AVATAR_MAX_EDGE. Returns the rel path under UPLOAD_DIR.
    Raises ValueError on anything unreadable."""
    name = uuid.uuid4().hex
    rel = f"avatars/{name}.jpg"
    dest = UPLOAD_DIR / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    try:
        with Image.open(tmp) as im:
            im.verify()
        with Image.open(tmp) as im:
            im = ImageOps.exif_transpose(im).convert("RGB")
            w, h = im.size
            side = min(w, h)
            x, y = (w - side) // 2, (h - side) // 2
            im = im.crop((x, y, x + side, y + side))
            if side > AVATAR_MAX_EDGE:
                im = im.resize((AVATAR_MAX_EDGE, AVATAR_MAX_EDGE),
                               Image.LANCZOS)
            _save_pixels(im, dest, "JPEG")
    except (UnidentifiedImageError, OSError):
        dest.unlink(missing_ok=True)
        raise ValueError("That file isn't a readable image.")
    return rel


def _store_profile_photo(media: UploadFile, user_id: int) -> str | None:
    """One profile-photo upload, pin-flow style: size cap, extension +
    real-bytes validation, random name, make_thumb (which physically
    uprights the stored original per EXIF and strips the flag).
    Returns an error string, or None on success."""
    ext = safe_ext(media.filename)
    if ext not in PHOTO_EXTS:
        return "Photos must be JPG, PNG, or WebP (10 MB max)."
    with get_conn(DB_PATH) as conn:
        count = conn.execute(
            "SELECT COUNT(*) AS n FROM profile_photos WHERE user_id = ?",
            (user_id,)).fetchone()["n"]
    if count >= PROFILE_PHOTO_MAX:
        return (f"Profiles hold at most {PROFILE_PHOTO_MAX} photos — "
                "delete one to add another.")
    try:
        tmp = save_upload(media, MAX_PHOTO_BYTES)
        try:
            with Image.open(tmp) as im:
                im.verify()
        except (UnidentifiedImageError, OSError):
            tmp.unlink(missing_ok=True)
            raise ValueError("That file isn't a readable image.")
        name = uuid.uuid4().hex
        rel = f"photos/{name}{ext}"
        dest = UPLOAD_DIR / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(tmp, dest)
        try:
            thumb_rel = make_thumb(dest, name)
        except (OSError, UnidentifiedImageError):
            dest.unlink(missing_ok=True)
            raise ValueError("Couldn't process that image.")
    except ValueError as e:
        return str(e)
    with get_conn(DB_PATH) as conn:
        conn.execute(
            "INSERT INTO profile_photos (user_id, path, thumb_path, "
            "created_at) VALUES (?, ?, ?, ?)",
            (user_id, rel, thumb_rel,
             datetime.now(timezone.utc).isoformat()))
        conn.commit()
    return None


@app.post("/profile/avatar", response_class=HTMLResponse)
async def profile_avatar_upload(request: Request,
                                avatar: UploadFile = File(None)):
    member = current_member(request)
    if not member:
        return RedirectResponse("/login?next=/profile/edit", status_code=303)
    if not avatar or not avatar.filename:
        return _edit_fail(request, member, "Pick a photo to upload first.")
    if safe_ext(avatar.filename) not in PHOTO_EXTS:
        return _edit_fail(request, member,
                          "Profile pictures must be JPG, PNG, or WebP "
                          "(10 MB max).")

    def _store() -> str | None:
        try:
            tmp = save_upload(avatar, MAX_PHOTO_BYTES)
            try:
                rel = _process_avatar(tmp)
            finally:
                tmp.unlink(missing_ok=True)
        except ValueError as e:
            return str(e)
        with get_conn(DB_PATH) as conn:
            old = conn.execute(
                "SELECT avatar_path FROM profiles WHERE user_id = ?",
                (member["id"],)).fetchone()
            conn.execute(
                "INSERT INTO profiles (user_id, avatar_path, updated_at) "
                "VALUES (?, ?, ?) ON CONFLICT(user_id) DO UPDATE SET "
                "avatar_path = excluded.avatar_path, "
                "updated_at = excluded.updated_at",
                (member["id"], rel,
                 datetime.now(timezone.utc).isoformat()))
            conn.commit()
        if old and old["avatar_path"] and old["avatar_path"] != rel:
            (UPLOAD_DIR / old["avatar_path"]).unlink(missing_ok=True)
        return None

    error = await run_in_threadpool(_store)
    if error:
        return _edit_fail(request, member, error)
    return RedirectResponse("/profile/edit", status_code=303)


@app.post("/profile/avatar/remove")
def profile_avatar_remove(request: Request):
    member = current_member(request)
    if not member:
        return RedirectResponse("/login?next=/profile/edit", status_code=303)
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT avatar_path FROM profiles WHERE user_id = ?",
            (member["id"],)).fetchone()
        conn.execute(
            "UPDATE profiles SET avatar_path = NULL, updated_at = ? "
            "WHERE user_id = ?",
            (datetime.now(timezone.utc).isoformat(), member["id"]))
        conn.commit()
    if row and row["avatar_path"]:
        (UPLOAD_DIR / row["avatar_path"]).unlink(missing_ok=True)
    return RedirectResponse("/profile/edit", status_code=303)


@app.post("/profile/photos", response_class=HTMLResponse)
async def profile_photo_upload(request: Request,
                               photo: UploadFile = File(None)):
    member = current_member(request)
    if not member:
        return RedirectResponse("/login?next=/profile/edit", status_code=303)
    if not photo or not photo.filename:
        return _edit_fail(request, member, "Pick a photo to upload first.")
    error = await run_in_threadpool(_store_profile_photo, photo, member["id"])
    if error:
        return _edit_fail(request, member, error)
    return RedirectResponse("/profile/edit#photos", status_code=303)


@app.post("/profile/photos/{photo_id}/delete")
def profile_photo_delete(request: Request, photo_id: int):
    member = current_member(request)
    if not member:
        return RedirectResponse("/login?next=/profile/edit", status_code=303)
    with get_conn(DB_PATH) as conn:
        row = conn.execute(
            "SELECT path, thumb_path FROM profile_photos "
            "WHERE id = ? AND user_id = ?", (photo_id, member["id"])).fetchone()
        if row:
            conn.execute("DELETE FROM profile_photos WHERE id = ?",
                         (photo_id,))
            conn.commit()
    if row:
        (UPLOAD_DIR / row["path"]).unlink(missing_ok=True)
        if row["thumb_path"]:
            (UPLOAD_DIR / row["thumb_path"]).unlink(missing_ok=True)
    return RedirectResponse("/profile/edit#photos", status_code=303)
