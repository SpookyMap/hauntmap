"""HauntMap v1 — mobile-first web app for sharing Halloween decorations.

Stack: FastAPI + Jinja2 + SQLite + local disk uploads. No user accounts in v1.
Voting is limited to one vote per browser per entry via cookie — this is a
SOFT limit only (cookies are trivially cleared); it stops casual double
voting, not determined abuse. See the vote route below.
"""
import calendar
import hashlib
import hmac
import logging
import os
import re
import requests
import secrets
import shutil
import sqlite3
import subprocess
import tempfile
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

from fastapi import BackgroundTasks, FastAPI, Form, HTTPException, Request, UploadFile, File
from fastapi.responses import FileResponse, HTMLResponse, JSONResponse, RedirectResponse, Response
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from PIL import Image, ImageOps, UnidentifiedImageError

from .db import get_conn, init_db
from . import sms_alerts
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

CATEGORIES = ("halloween", "christmas", "halloween_stores", "restaurants", "coffee", "shops", "parks", "haunted_houses", "events", "live")
CAT_LABELS = {"halloween": "Halloween", "christmas": "Christmas",
              "halloween_stores": "Halloween Stores",
              "restaurants": "Restaurhaunts", "coffee": "Coffee & Cafes",
              "shops": "Shops", "parks": "Parks",
              "haunted_houses": "Haunted Houses",
              "events": "Events", "live": "Live Streams"}
CAT_EMOJI = {"halloween": "🎃", "christmas": "🎄", "halloween_stores": "👻",
             "restaurants": "🍽️", "coffee": "☕", "shops": "🛍️", "parks": "🌳",
             "haunted_houses": "🏚️", "events": "🎪", "live": "🔴"}

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
def _healthz():
    """Render health-check target: DB-independent, 200 whenever the process
    is up, so a deploy only takes traffic once the new instance serves."""
    return {"status": "ok"}


@app.middleware("http")
async def _cache_headers(request: Request, call_next):
    """Media/static filenames are unique per upload, so browsers and the
    Cloudflare edge may cache them for 30 days instead of re-pulling from
    origin on every visit (was: no origin header -> 4h default). HTML is
    untouched and stays fresh."""
    response = await call_next(request)
    if request.url.path.startswith(("/media/", "/static/")):
        response.headers["Cache-Control"] = "public, max-age=2592000"
    return response


@app.middleware("http")
async def _track_page_view(request: Request, call_next):
    """Log page views for the admin traffic dashboard. Skips static/media/admin, logged-in admin visits, and Jarvis's own verification checks."""
    response = await call_next(request)
    try:
        if request.method == "GET" and response.status_code == 200:
            path = request.url.path
            if not path.startswith(("/media", "/static", "/admin", "/favicon")):
                if request.cookies.get(ADMIN_COOKIE) not in admin_sessions and \
                   "HauntMap-Verify" not in request.headers.get("user-agent", ""):
                    with get_conn(DB_PATH) as conn:
                        conn.execute(
                            "CREATE TABLE IF NOT EXISTS page_views (id INTEGER PRIMARY KEY, path TEXT, viewed_at TEXT, referrer TEXT)"
                        )
                        for col in ("referrer", "device", "sid"):
                            try:
                                conn.execute(f"ALTER TABLE page_views ADD COLUMN {col} TEXT")
                            except Exception:
                                pass  # column already exists
                        referrer = request.headers.get("referer", "")[:500]
                        ua = request.headers.get("user-agent", "")[:500]
                        # Simple device detection from user agent
                        ua_lower = ua.lower()
                        if "iphone" in ua_lower or "ipad" in ua_lower:
                            device = "iOS"
                        elif "android" in ua_lower:
                            device = "Android"
                        elif "windows" in ua_lower:
                            device = "Windows"
                        elif "macintosh" in ua_lower or "mac os" in ua_lower:
                            device = "Mac"
                        elif "linux" in ua_lower:
                            device = "Linux"
                        else:
                            device = "Other"
                        sid = request.cookies.get("hm_sid")
                        new_sid = not sid
                        if new_sid:
                            sid = secrets.token_hex(16)
                        conn.execute(
                            "INSERT INTO page_views (path, viewed_at, referrer, device, sid) VALUES (?, ?, ?, ?, ?)",
                            (path, datetime.now(timezone.utc).isoformat(), referrer, device, sid),
                        )
                        conn.commit()
                        if new_sid:
                            response.set_cookie("hm_sid", sid, max_age=30 * 24 * 3600,
                                                httponly=True, samesite="lax")
    except Exception:
        pass  # never break a page load for analytics
    return response


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


def _views_by_id(conn) -> dict:
    return {r["eid"]: r["views"] for r in conn.execute(_VIEWS_GROUP_SQL)}


def _attach_views(conn, entries: list) -> list:
    """Set ``_views`` (all-time /d/{id} views, 0 when never viewed) on
    each entry dict, using a single grouped page_views query."""
    if not entries:
        return entries
    views = _views_by_id(conn)
    for e in entries:
        e["_views"] = views.get(e["id"], 0)
    return entries


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


def category_peers(entry: dict) -> list[dict]:
    """All other visible entries in the entry's category (row dicts)."""
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT * FROM entries WHERE hidden = 0 AND category = ? AND id != ?",
            (entry["category"], entry["id"]),
        ).fetchall()
    return [row_to_dict(r) for r in rows]


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


def has_footage(entry: dict) -> bool:
    """Footage predicate for the video chain (Item 3 spec): a TikTok
    /video/ URL or an uploaded video file. Deliberately narrower than the
    homepage "Has video" filter (any tiktok_url) — a live/profile TikTok
    link is not playable footage of the haunt."""
    tt = entry.get("tiktok_url") or ""
    return "/video/" in tt or entry.get("media_type") == "video"


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


def _town_inventory(conn, category: str = "halloween") -> list[dict]:
    """Every visible town in a category as {label, city, state, count,
    clat, clng} — the label/city/state come from the same extract_*
    helpers that build card town_labels, and the centroid is the mean of
    the town's pin coordinates (all halloween pins carry coords today)."""
    inv: dict[str, dict] = {}
    for r in conn.execute(
            "SELECT town, lat, lng FROM entries "
            "WHERE hidden = 0 AND category = ?", (category,)).fetchall():
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


def _resolve_visitor_area(inventory: list[dict], geo: dict | None) -> dict:
    """Resolve the visitor's area against the town inventory.

    Resolution order (Item 1 spec):
      (a) exact town match — a mapped town whose city equals the header
          city (in the header state, when known);
      (b) nearest towns by haversine from the header lat/lng, within
          _GEO_NEAR_RADIUS_MI;
      (c) biggest towns in the visitor's state;
      (d) today's behaviour — biggest towns site-wide ("fallback").
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
            "chips": fallback_chips, "area_labels": set()}
    if not geo:
        return base
    city = (geo.get("city") or "").strip()
    state = geo.get("state") or ""
    vlat, vlng = geo.get("lat"), geo.get("lng")
    city_disp = _smart_case_city(city) if city else ""
    state_name = US_STATE_NAMES.get(state, state)

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
    if exact is not None:
        alat = vlat if vlat is not None else exact["clat"]
        alng = vlng if vlng is not None else exact["clng"]
        neighbours: list[dict] = []
        if alat is not None and alng is not None:
            scored = []
            for t in inventory:
                if t["label"] == exact["label"]:
                    continue
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
                "sub": f"Closest haunt towns to {city_disp} first — "
                       "tap a town to see its haunts, or change your area.",
                "chips": chips_of(chips), "area_labels": area}
    # (b) nearest towns to the header coordinates
    if vlat is not None and vlng is not None:
        scored = []
        for t in inventory:
            d = dist_to(t, vlat, vlng)
            if d is not None and d <= _GEO_NEAR_RADIUS_MI:
                scored.append((d, t))
        if scored:
            near = [t for _d, t in sorted(
                scored, key=lambda x: (x[0], -x[1]["count"], x[1]["label"]))]
            chips = list(near)
            if len(chips) < 8 and state:
                have = {t["label"] for t in chips}
                for t in biggest:
                    if len(chips) >= 8:
                        break
                    if t["state"] == state and t["label"] not in have:
                        chips.append(t)
                        have.add(t["label"])
            area_name = (f"{city_disp} area" if city_disp
                         else (state_name or "your area"))
            return {"mode": "near",
                    "area_name": area_name,
                    "heading": f"Near You — {area_name}",
                    "sub": f"Closest haunt towns to {area_name} first — "
                           "tap a town to see its haunts, or change your area.",
                    "chips": chips_of(chips),
                    "area_labels": {t["label"] for t in near}}
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
                    "area_labels": {t["label"] for t in in_state}}
    # Known area, zero mapped supply: name it honestly, show fallback towns.
    if city or state:
        area_name = f"{city_disp} area" if city_disp else state_name
        return {"mode": "nomap",
                "area_name": area_name,
                "heading": f"Near You — {area_name}",
                "sub": f"No haunts mapped near {area_name} yet — add yours "
                       "or request your town below. Meanwhile, the biggest "
                       "haunt towns on the map:",
                "chips": fallback_chips, "area_labels": set()}
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
    query = "SELECT * FROM entries WHERE hidden = 0 AND category = ?"
    params: list = [cat]
    if scare in ("family", "spooky", "creepy", "terrifying", "extreme"):
        query += " AND scare_level = ?"
        params.append(scare)
    if tag in ("animatronics", "inflatables", "handmade", "walkthrough",
               "projector", "lights", "music", "street-wide", "multi-house",
               "ticketed", "2025", "market", "oddities", "witchy", "craft",
               "flea", "free", "flagship", "21+"):
        query += " AND (',' || COALESCE(tags,'') || ',') LIKE ?"
        params.append(f"%,{tag},%")
    if video.strip() == "1":
        query += (" AND ((tiktok_url IS NOT NULL AND TRIM(tiktok_url) != '')"
                  " OR LOWER(media_path) LIKE '%.mp4'"
                  " OR LOWER(media_path) LIKE '%.webm'"
                  " OR LOWER(media_path) LIKE '%.mov')")
    with get_conn(DB_PATH) as conn:
        rows = [row_to_dict(r) for r in conn.execute(query, params).fetchall()]
        _attach_views(conn, rows)  # Item 7: area-led feed cards carry counts
    rows = [e for e in rows if e["town_label"] in area_labels]
    rows.sort(key=lambda e: e.get("created_at") or "", reverse=True)
    if sort == "top":
        rows.sort(key=lambda e: -(e.get("votes") or 0))
    rows.sort(key=lambda e: 0 if _feed_has_video(e) else 1)
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
    s = (title.replace("\u2013", "-").replace("\u2014", "-")
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


def _events_on_count(conn, town_label: str, on_date) -> int:
    """Parsed events covering `on_date` whose town_label (the same
    extract_city_state label every card shows) equals `town_label`."""
    n = 0
    for r in conn.execute(
            "SELECT title, town FROM entries "
            "WHERE hidden = 0 AND category = 'events'").fetchall():
        label = extract_city_state(r["town"] or "") or r["town"] or ""
        if label == town_label and event_on_date(r["title"], on_date):
            n += 1
    return n


def _tonight_strip(town_label: str, displays: int, town_note: str = "") -> dict:
    """Data for the _tonight_strip.html partial (Item 5): ET countdown,
    events on tonight near the anchor town, displays lit tonight.
    `displays` = halloween-category pins in the town (house displays run
    nightly through the season, so every display pin counts as lit)."""
    today = _today_et()
    halloween = _mkdate(today.year, 10, 31)
    days = (halloween - today).days
    if days > 1:
        countdown = f"\U0001F383 {days} days to Halloween"
    elif days == 1:
        countdown = "\U0001F383 1 day to Halloween"
    elif days == 0:
        countdown = "\U0001F383 It's Halloween night!"
    else:
        countdown = "\U0001F383 Halloween night has passed — still lit tonight"
    with get_conn(DB_PATH) as conn:
        events_on = _events_on_count(conn, town_label, today)
    return {"town_label": town_label, "town_note": town_note,
            "countdown": countdown, "today_iso": today.isoformat(),
            "events_on": events_on, "displays": displays}


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
    out = {"next_pin": None, "prev_pin": None, "more_near": [], "more_like": []}
    coord: list[dict] = []
    if entry.get("lat") is not None and entry.get("lng") is not None:
        coord = [p for p in peers
                 if p.get("lat") is not None and p.get("lng") is not None]
        for p in coord:
            p["distance"] = haversine_miles(
                entry["lat"], entry["lng"], p["lat"], p["lng"])
        coord.sort(key=lambda p: (p["distance"], p["id"]))
        out["more_near"] = coord[:6]
        out["next_pin"] = coord[0] if coord else None
        # Prev = the closest pin whose OWN nearest neighbour is this pin
        # (reciprocal nearest) — the step a chain-walker came from. Bounded
        # to the 40 closest candidates so the check stays cheap.
        if coord:
            everyone = coord + [entry]
            for cand in coord[:40]:
                best_id, best_d = None, None
                for q in everyone:
                    if q["id"] == cand["id"]:
                        continue
                    d = haversine_miles(cand["lat"], cand["lng"],
                                        q["lat"], q["lng"])
                    if best_d is None or d < best_d:
                        best_d, best_id = d, q["id"]
                if best_id == entry["id"]:
                    out["prev_pin"] = cand
                    break
    # Retention Wave 1, Item 3 (video chain): when THIS pin has footage,
    # the primary Next target chains to ANOTHER pin with footage (same
    # predicate) instead of the nearest pin of any kind, and the
    # under-player strip lists those nearby footage pins. The radius cap
    # keeps "near" honest — beyond it the caller falls back to the plain
    # geographic next above. WHICH footage pin leads the chain is the
    # most-viewed one (see the Dan note inside the block below).
    out["next_video_pin"] = None
    out["more_videos"] = []
    out["video_chain"] = []
    out["town_centers"] = []
    if has_footage(entry):
        # `coord` is already distance-sorted and carries `distance`.
        vids = [p for p in coord
                if has_footage(p) and p["distance"] <= VIDEO_CHAIN_RADIUS_MI]
        out["more_videos"] = vids[:6]
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
        # `more_videos` (the "More videos near here" strip) stays
        # nearest-first, as its label says.
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


def towns(category: str = "halloween", state: str = "") -> list[str]:
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

def _tonight_pool(conn, category: str | None) -> list[dict]:
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
def home(request: Request, sort: str = "top", town: str = "", town_search: str = "",
         state: str = "", region: str = "", cat: str = "halloween", scare: str = "", tag: str = "",
         video: str = ""):
    cat = cat if cat in CATEGORIES else "halloween"
    sort = sort if sort in ("top", "new") else "top"
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
    # the stable secondary order within each group.
    video_first = (
        "CASE WHEN ((tiktok_url IS NOT NULL AND TRIM(tiktok_url) != '')"
        " OR LOWER(media_path) LIKE '%.mp4'"
        " OR LOWER(media_path) LIKE '%.webm'"
        " OR LOWER(media_path) LIKE '%.mov') THEN 0 ELSE 1 END")
    query += f" ORDER BY {video_first}, {order} LIMIT 100"
    with get_conn(DB_PATH) as conn:
        entries = [row_to_dict(r) for r in conn.execute(query, params).fetchall()]
        _attach_views(conn, entries)  # Item 7: feed cards show view counts
        sponsors = [dict(r) for r in conn.execute(
            "SELECT * FROM sponsors WHERE is_active = 1 ORDER BY "
            "CASE tier WHEN 'title' THEN 0 WHEN 'premium' THEN 1 ELSE 2 END, created_at").fetchall()]
    # Item 1: resolve the visitor's area once — it drives both the
    # Near-you module (below) and the feed lead. With geo=None this is
    # exactly today's biggest-towns-site-wide behaviour.
    with get_conn(DB_PATH) as conn:
        halloween_inventory = _town_inventory(conn, "halloween")
    resolved_area = _resolve_visitor_area(halloween_inventory, geo)
    if geo and resolved_area["area_labels"]:
        # Lead the default feed with the visitor's area: area pins first
        # (in normal feed order), then the regular feed de-duped behind
        # them, still capped at 100 — the feed is re-led, never emptied.
        area_labels = resolved_area["area_labels"]
        if cat != "halloween":
            with get_conn(DB_PATH) as conn:
                cat_inventory = _town_inventory(conn, cat)
            area_labels = _resolve_visitor_area(cat_inventory, geo)["area_labels"]
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
        trows = conn.execute(
            "SELECT e.*, COALESCE(v.views, 0) AS _views FROM entries e "
            "LEFT JOIN (SELECT CAST(substr(path, 4) AS INTEGER) AS eid, "
            "                  COUNT(*) AS views FROM page_views "
            "                  WHERE path LIKE '/d/%' GROUP BY eid) v "
            "  ON v.eid = e.id "
            "WHERE e.hidden = 0 AND e.media_path IS NOT NULL "
            "  AND TRIM(e.media_path) != '' "
            "ORDER BY _views DESC, e.votes DESC, e.id LIMIT 5").fetchall()
        trending = [row_to_dict(r) for r in trows if r["_views"] > 0]
        # Near-you towns now come from the Item 1 resolution (geo-aware
        # when Cloudflare headers are present, biggest-site-wide when
        # not) computed above; the counts are the same live halloween
        # town counts this block used to compute inline.
        near_towns = resolved_area["chips"]
    # Retention Wave 3, Item 5: the "Tonight" strip's anchor town.
    # Resolution: the visitor's explicit ?town= context first; then Item
    # 1's geo-resolved anchor (the first Near-you chip in exact/near/
    # state mode — that town leads the chips); else the biggest town on
    # the map, labelled honestly via town_note (this also covers Item
    # 1's "nomap" mode: the visitor's own area has no supply, so the
    # strip names the biggest town AS the biggest town, never as "near
    # you"). Displays = halloween pins in the anchor town, counted from
    # the same inventory that builds the Near-you chips.
    strip_label, strip_note = "", ""
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
        strip_label = resolved_area["chips"][0]["label"]
        hit = next((t for t in halloween_inventory
                    if t["label"] == strip_label), None)
        strip_displays = hit["count"] if hit else 0
    elif halloween_inventory:
        biggest = max(halloween_inventory,
                      key=lambda t: (t["count"], t["label"]))
        strip_label = biggest["label"]
        strip_displays = biggest["count"]
        strip_note = "biggest town on the map"
    tstrip = (_tonight_strip(strip_label, strip_displays, strip_note)
              if strip_label else None)
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
         "bracket_teaser": _bracket_teaser(),
         "trending": trending, "near_towns": near_towns,
         "near_heading": resolved_area["heading"],
         "near_sub": resolved_area["sub"],
         "geo_mode": resolved_area["mode"],
         "geo_area": resolved_area["area_name"],
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
         "bottom_tabs": _place_tabs(cat, state, region, sort, scare, tag,
                                    "1" if video.strip() == "1" else ""),
         "tier_labels": {"featured": "Featured Sponsor", "premium": "Premium Sponsor", "title": "Title Sponsor"}},
    )
    if tonight:
        response.set_cookie("tonight_last", str(tonight["id"]),
                            max_age=7 * 24 * 3600, path="/", samesite="lax")
    return response


@app.get("/events", response_class=HTMLResponse)
def events_page(request: Request, type: str = "", genre: str = "",
                venue: str = "", sort: str = "top",
                state: str = "", town: str = "", region: str = "",
                on: str = ""):
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
    with get_conn(DB_PATH) as conn:
        # Location maps over every visible event: derived state / city
        # label -> event count + the raw town strings that produce it.
        state_counts: dict[str, int] = {}
        town_counts: dict[str, int] = {}
        town_state: dict[str, str] = {}
        raw_by_state: dict[str, list] = {}
        raw_by_town: dict[str, list] = {}
        town_groups: list = []
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
        # term appearing anywhere in the raw town string.
        region_counts = {
            slug: sum(n for raw, n in town_groups
                      if any(t in raw.lower()
                             for t in _region_terms(slug)))
            for slug, _label in REGION_TABS}
        if region:
            raws = [raw for raw, _n in town_groups
                    if any(t in raw.lower() for t in region_terms)]
            if raws:
                query += f" AND town IN ({','.join('?' * len(raws))})"
                params += raws
            else:
                query += " AND 1 = 0"
        # With a date view active the SQL cap comes off (the events
        # catalogue is ~553 rows): the Python date filter below runs
        # over the full facet/town-filtered set, then caps at 100.
        query += f" ORDER BY {video_first}, {order}"
        if on_date is None:
            query += " LIMIT 100"
        entries = [row_to_dict(r) for r in conn.execute(query, params).fetchall()]
        counts: dict[str, dict[str, int]] = {}
        for key, col, _values, _labels in EVENT_FACETS:
            counts[key] = {r[col]: r["n"] for r in conn.execute(
                f"SELECT {col}, COUNT(*) AS n FROM entries "
                f"WHERE hidden = 0 AND category = 'events' AND {col} IS NOT NULL "
                f"GROUP BY {col}").fetchall()}
        total = conn.execute(
            "SELECT COUNT(*) AS n FROM entries "
            "WHERE hidden = 0 AND category = 'events'").fetchone()["n"]
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
    return templates.TemplateResponse(request, "events.html",
        {"request": request, "entries": entries, "sort": sort,
         "facets": facets, "selected": selected, "total": total,
         "loc": loc,
         "filtered": any(selected.values()) or bool(state) or bool(town)
                     or bool(region) or bool(on_date),
         "on": on_str, "on_label": on_label, "on_total": on_total,
         "voted": voted})


@app.get("/markets", response_class=HTMLResponse)
def markets_page(request: Request):
    # Flea Markets & Pop-Ups (Dan, Oct 23): every event pin faceted
    # ev_type='Market' on one page, soonest first. Event dates live in
    # the titles, so ordering reuses parse_event_dates (the same parser
    # behind the /events ?on= view); undated titles sort last, by votes.
    # The set is small (dozens), so no cap is needed.
    with get_conn(DB_PATH) as conn:
        entries = [row_to_dict(r) for r in conn.execute(
            "SELECT * FROM entries WHERE hidden = 0 AND category = 'events' "
            "AND ev_type = 'Market'").fetchall()]

    def _soonest(e):
        span = parse_event_dates(e["title"])
        if span:
            return (0, span[0].toordinal(), -(e["votes"] or 0), e["id"])
        return (1, 0, -(e["votes"] or 0), e["id"])

    entries.sort(key=_soonest)
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    return templates.TemplateResponse(request, "markets.html",
        {"request": request, "entries": entries, "total": len(entries),
         "voted": voted})


RESTAURHAUNT_CATS = ("restaurants", "coffee", "shops")


@app.get("/restaurhaunts", response_class=HTMLResponse)
def restaurhaunts(request: Request, sort: str = "top", f: str = "all",
                  town_search: str = ""):
    # Combined "Restaurhaunts & Cafes" listing (Dan, Oct 22): one mixed
    # feed over the existing restaurants + coffee + shops categories
    # (bars live in restaurants). Category keys are unchanged — only the
    # display word became "restaurhaunts". Each card carries its own
    # category chip so the mix stays legible.
    sort = sort if sort in ("top", "new") else "top"
    f = f if f in ("all",) + RESTAURHAUNT_CATS else "all"
    order = "votes DESC, created_at DESC" if sort == "top" else "created_at DESC"
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
    query += f" ORDER BY {order} LIMIT 100"
    with get_conn(DB_PATH) as conn:
        entries = [row_to_dict(r) for r in conn.execute(query, params).fetchall()]
        counts = {c: 0 for c in RESTAURHAUNT_CATS}
        for r in conn.execute(
                "SELECT category, COUNT(*) AS n FROM entries "
                "WHERE hidden = 0 AND category IN ('restaurants', 'coffee', 'shops') "
                "GROUP BY category").fetchall():
            counts[r["category"]] = r["n"]
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    return templates.TemplateResponse(request, "restaurhaunts.html",
        {"request": request, "entries": entries, "sort": sort, "f": f,
         "town_search": town_search, "counts": counts, "voted": voted,
         "total": sum(counts.values()),
         "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI})


@app.get("/upload", response_class=HTMLResponse)
def upload_form(request: Request):
    return templates.TemplateResponse(request, "upload.html", {"request": request, "error": None})


@app.get("/nearby", response_class=HTMLResponse)
def nearby(request: Request, q: str = "", miles: float = 10, cat: str = "halloween",
           sort: str = "top", lat: str = "", lng: str = ""):
    cat = cat if cat in CATEGORIES else "halloween"
    sort = sort if sort in ("top", "new") else "top"
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
        with get_conn(DB_PATH) as conn:
            rows = conn.execute(
                "SELECT * FROM entries WHERE hidden = 0 AND category = ? "
                "AND lat IS NOT NULL AND lng IS NOT NULL", [cat]).fetchall()
        clat, clng = center
        for r in rows:
            d = row_to_dict(r)
            d["distance"] = haversine_miles(clat, clng, r["lat"], r["lng"])
            if d["distance"] <= miles:
                entries.append(d)
        order = "votes DESC, created_at DESC" if sort == "top" else "created_at DESC"
        # sort by distance first, then the chosen order
        entries.sort(key=lambda e: (e["distance"],
                                    -e["votes"] if sort == "top" else e["created_at"]))
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    return templates.TemplateResponse(request, "nearby.html",
        {"request": request, "entries": entries, "q": q, "miles": miles,
         "err": err, "voted": voted, "cat": cat, "cat_labels": CAT_LABELS,
         "cat_emoji": CAT_EMOJI, "sort": sort},
    )


@app.get("/map", response_class=HTMLResponse)
def map_view(request: Request, cat: str = "halloween"):
    """Full-screen map with all haunt pins, Google Maps-style browsing."""
    cat = cat if cat in CATEGORIES else "halloween"
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT * FROM entries WHERE hidden = 0 AND category = ? "
            "AND lat IS NOT NULL AND lng IS NOT NULL", [cat]).fetchall()
    pins = [row_to_dict(r) for r in rows]
    return templates.TemplateResponse(request, "map.html",
        {"request": request, "pins": pins, "cat": cat,
         "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI},
    )


DIY_VIDEOS = [
    {"title": "DIY Circus Tent — Halloween Party Build", "creator": "Taylor Booth (@theballoonchickaz)", "url": "https://www.tiktok.com/@theballoonchickaz/video/7698864214865087775", "video_id": "7698864214865087775", "blurb": "A full-size circus tent, built from scratch for a Halloween party — Taylor's whole process in 85 seconds. 229K views and counting, and you'll see why."},
    {"title": "Fog Chiller DIY — Maiden Voyage", "creator": "@theblackirishouse", "url": "https://www.tiktok.com/@theblackirishouse/video/7693254709972372767", "video_id": "7693254709972372767", "blurb": "Chill your fog machine's output and the fog hugs the ground like a graveyard at dawn. This build's first run shows exactly how it's done."},
    {"title": "Pirate Skeleton DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7698131249034005774", "video_id": "7698131249034005774", "blurb": "Another Halloween DIY — and it might be her favorite yet. Pirate bones done right."},
    {"title": "Witch's Cauldron DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7698064196147236109", "video_id": "7698064196147236109", "blurb": "Every witch needs a cauldron — and this one may have gotten a little carried away."},
    {"title": "Best Halloween DIYs in 20 Seconds", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7698024441569234190", "video_id": "7698024441569234190", "blurb": "Months of crafting, creativity and chaos in one rapid-fire highlight reel."},
    {"title": "Boo-zy Bones Drinking Skeletons", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7697775692141890829", "video_id": "7697775692141890829", "blurb": "These skeletons have been drinking for centuries…"},
    {"title": "Peeing Skeleton Dog DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7697651205543169294", "video_id": "7697651205543169294", "blurb": "Even in the afterlife, dogs still gotta go."},
    {"title": "Haunted Dollhouse DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7697030306649492749", "video_id": "7697030306649492749", "blurb": "Who knew a 1991 Playskool dollhouse could turn into something so creepy?"},
    {"title": "The Boo-zy Skeleton Fountain", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7696649206160837902", "video_id": "7696649206160837902", "blurb": "A skeleton chilling in a bubbling green fountain — the porch centerpiece your neighbors will copy next year."},
    {"title": "Slimed House DIY", "creator": "@wyldwoodsdiy", "url": "https://www.tiktok.com/@wyldwoodsdiy/video/7693296146705403149", "video_id": "7693296146705403149", "blurb": "She slimed her whole house for Halloween — gutters and all — and it turned out amazing."},
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
]

DIY_VIDEOS_NICK = [
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


@app.get("/diy", response_class=HTMLResponse)
def diy_page(request: Request):
    return templates.TemplateResponse(
        request, "diy.html", {"videos": DIY_VIDEOS, "nick_videos": DIY_VIDEOS_NICK},
    )


# ------------------------------------------------------------- diy costumes
# Curated costume ideas (Dan, Oct 22): OUR OWN short write-ups only — the full
# step-by-step instructions live at each credited source, linked from every
# card. PHOTOS ARE NEVER OURS AND NEVER COPIED (Dan, Oct 22 rework): every
# card shows the creator's own photo or video through the platform's official
# embed — a Pinterest pin embed ("pin" = pin id) or a YouTube click-to-play
# facade ("yt" = video id) — served by the platform with the creator's credit
# and link-back. Tutorials with no embeddable post of the costume are NOT
# shown; they sit on the permission-ask list
# (files/diy-costumes-permission-asks.md) until the creator says yes.

COSTUME_SECTIONS = [
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

DUEL_EXCLUDE_IDS = frozenset({197, 210, 228, 235, 239, 244, 245, 246, 250, 251, 253, 260, 265, 270, 278, 279, 280, 282, 283, 284, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 924, 925, 926, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1273, 1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2064, 2073, 2081, 2082, 2084, 2094, 2098, 2100, 2101, 2104, 2106, 2107, 2108, 2109, 2110, 2112, 2119, 2120, 2121, 2122, 2126, 2127, 2130, 2131, 2133, 2134, 2135, 2136, 2137, 2140, 2142, 2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2155, 2156, 2160, 2162, 2168, 2169, 2170, 2172, 2174, 2178, 2179, 2181, 2182, 2186, 2193, 2199, 2202, 2204, 2205, 2206, 2208, 2209, 2211, 2214, 2217, 2221, 2226, 2227, 2228, 2230, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239, 2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2251, 2252, 2253, 2254, 2255, 2256, 2257, 2258, 2259, 2260, 2261, 2262, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271, 2272, 2273, 2274, 2275, 2276, 2277, 2280, 2284, 2288, 2291, 2292, 2293, 2294, 2295, 2296, 2300, 2302, 2311, 2312, 2313, 2315, 2320, 2321, 2322, 2323, 2324, 2327, 2328, 2329, 2330, 2332, 2333, 2334, 2335, 2336, 2337, 2338, 2340, 2341, 2343, 2347, 2348, 2350, 2352, 2359, 2363, 2364, 2365, 2366, 2367, 2368, 2369, 2371, 2374, 2375, 2376, 2377, 2379, 2380, 2381, 2386, 2389, 2397, 2398, 2399, 2404, 2405, 2406, 2412, 2417, 2418, 2420, 2421, 2422, 2423, 2431, 2432, 2438, 2440, 2441, 2443, 2444, 2446, 2449, 2450, 2455, 2457, 2460, 2463, 2465, 2470, 2475, 2476, 2478, 2479, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2490, 2491, 2492, 2493, 2494, 2495, 2497, 2498, 2499, 2500, 2501, 2502, 2505, 2506, 2507, 2508, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2531, 2533, 2534, 2537, 2539, 2540, 2541, 2542, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559, 2560, 2561, 2562, 2563, 2564, 2575, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2590, 2591, 2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2635, 2636, 2637, 2638, 2639, 2640, 2644, 2646, 2649, 2656, 2659, 2662, 2668, 2669, 2670, 2671, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2684, 2686, 2687, 2688, 2691, 2694, 2695, 2699, 2700, 2701, 2702, 2703, 2704, 2705, 2707, 2708, 2709, 2710, 2711, 2712, 2715, 2716, 2717, 2718, 2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2746, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767, 2770, 2771, 2772, 2773, 2774, 2777, 2778, 2779, 2782, 2783, 2784, 2786, 2787, 2788, 2790, 2794, 2795, 2796, 2797, 2798, 2799, 2801, 2802, 2803, 2805, 2807, 2811, 2812, 2813, 2814, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2828, 2832, 2833, 2834, 2835, 2836, 2837, 2839, 2842, 2843, 2845, 2847, 2848, 2854, 2855, 2856, 2857, 2860, 2862, 2863, 2864, 2866, 2870, 2871, 2872, 2874, 2876, 2877, 2879, 2880, 2881, 2886, 2888, 2889, 2890, 2891, 2893, 2894, 2896, 2898, 2900, 2901, 2902, 2905, 2907, 2908, 2909, 2910, 2911, 2912, 2914, 2915, 2916, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927, 2928, 2929, 2931, 2932, 2933, 2934, 2935, 2937, 2938, 2939, 2940, 2941, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2964, 2965, 2968, 2969, 2970, 2974, 2975, 2976, 2978, 2979, 2980, 2981, 2982, 2983, 2986, 2987, 2988, 2989, 2991, 2992, 2998, 2999, 3000, 3003, 3004, 3006, 3007, 3009, 3010, 3011, 3013, 3014, 3015, 3016, 3017, 3019, 3020, 3025, 3026, 3034, 3035, 3036, 3039, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3057, 3058, 3059, 3060, 3061, 3062, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3076, 3077, 3082, 3083, 3085, 3086, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3108, 3109, 3110, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3132, 3134, 3135, 3137, 3138, 3139, 3144, 3145, 3146, 3147, 3148, 3149, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3161, 3162, 3163, 3164, 3165, 3169, 3170, 3171, 3172, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3186, 3188, 3189, 3190, 3191, 3192, 3195, 3196, 3197, 3202, 3203, 3210, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3240, 3241, 3242, 3243, 3244, 3245, 3246, 3247, 3248, 3254, 3256, 3257, 3258, 3260, 3261, 3266, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3278, 3279, 3280, 3282, 3283, 3288, 3289, 3290, 3291, 3292, 3293, 3295, 3297, 3299, 3300, 3301, 3302, 3303, 3304, 3305, 3312, 3314, 3319, 3320, 3324, 3325, 3326, 3327, 3332, 3333, 3334, 3336, 3337, 3338, 3340, 3343, 3346, 3348, 3352, 3353, 3354, 3355, 3356, 3357, 3359, 3360, 3361, 3362, 3364, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3379, 3380, 3382, 3385, 3387, 3388, 3390, 3391, 3394, 3397, 3398, 3402, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423, 3424, 3427, 3428, 3429, 3432, 3435, 3438, 3439, 3443, 3444, 3445, 3447, 3449, 3450, 3451, 3453, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3466, 3474, 3477, 3482, 3484, 3485, 3489, 3490, 3492, 3497, 3498, 3500, 3501, 3502, 3504, 3506, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3521, 3522, 3523, 3524, 3527, 3529, 3531, 3532, 3537, 3540, 3545, 3546, 3548, 3551, 3552, 3554, 3555, 3556, 3559, 3568, 3570, 3571, 3572, 3573, 3620, 3636, 3667, 3673, 3674, 3724, 3741, 3911, 3925, 3936, 3938, 3993, 4014, 4053, 4058, 4077, 4488, 4489, 4491, 4493, 4494, 4496, 4498, 4500, 4502, 4503, 4505, 4507, 4509, 4511, 4513, 4514, 4516, 4518, 4520, 4522, 4523, 4525, 4527, 4529, 4531, 4532, 4534, 4536, 4538, 4540, 4542, 4543, 4545, 4547, 4549, 4551, 4553, 4555, 4798, 4800, 4802, 4804, 4806, 4808, 4810, 4811, 4812, 4813, 4814, 4815, 4816, 4817, 4818, 4819, 4820, 4821, 4822, 4823, 4824, 4825, 4826, 4827, 4828, 4829, 4830, 4831, 4832, 4833, 4839, 4841, 4843, 4844, 4846, 4848, 4850, 4851, 4853, 4855, 4856, 4978, 4986, 4989, 5067, 5071, 5073, 5074, 5075, 5080, 5082, 5083, 5085, 5086, 5087, 5088, 5089, 5092, 5093, 5094, 5096, 5097, 5098, 5099, 5100, 5101, 5102, 5105, 5524, 5525, 5526, 5527, 5528, 5529, 5530, 5531, 5532, 5533, 5534, 5535, 5536, 5538})  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)

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


@app.get("/games", response_class=HTMLResponse)
def games_page(request: Request):
    return templates.TemplateResponse(request, "games.html", {})


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
    server renders the pool MOST-VIEWED first (all-time detail-page
    views, the Trending measure — that is also the final order when
    the visitor's town is unknown). When the visitor's town IS known
    (localStorage 'hm_town' — the server never sees it), watch.html
    re-orders client-side from the payload below: most-viewed footage
    within VIDEO_CHAIN_RADIUS_MI of the visitor first, nearest to the
    visitor breaking ties, the rest in server order behind — the same
    anchoring detail_chain's video chain uses. This supersedes the
    Oct 21 per-visit shuffle. Every slide also carries _views for
    Item 7's count chips (one grouped LEFT JOIN, as in Trending)."""
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT e.*, COALESCE(v.views, 0) AS _views FROM entries e "
            "LEFT JOIN (SELECT CAST(substr(path, 4) AS INTEGER) AS eid, "
            "                  COUNT(*) AS views FROM page_views "
            "                  WHERE path LIKE '/d/%' GROUP BY eid) v "
            "  ON v.eid = e.id "
            "WHERE e.hidden = 0 AND ("
            "(e.tiktok_url IS NOT NULL AND e.tiktok_url LIKE '%/video/%')"
            " OR LOWER(e.media_path) LIKE '%.mp4'"
            " OR LOWER(e.media_path) LIKE '%.webm'"
            " OR LOWER(e.media_path) LIKE '%.mov')"
            " ORDER BY _views DESC, e.votes DESC, e.id LIMIT 60").fetchall()
    entries = [row_to_dict(r) for r in rows]
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


def _vt_video_pool(conn) -> list[dict]:
    """Playable-video pins eligible for a Virtual Tour: a TikTok /video/
    URL or an uploaded video file, with a thumbnail and map coordinates,
    never 2025-tagged (the same currency rule as Tonight's Display). Each
    dict carries _views (detail-page views) as the popularity signal —
    votes are near-zero on video pins, views are what actually rank them.
    A display listed twice (same title + town) appears once."""
    rows = conn.execute(
        """SELECT e.*, COALESCE(v.views, 0) AS _views FROM entries e
           LEFT JOIN (SELECT CAST(substr(path, 4) AS INTEGER) AS eid,
                             COUNT(*) AS views
                      FROM page_views WHERE path LIKE '/d/%' GROUP BY eid) v
             ON v.eid = e.id
           WHERE e.hidden = 0
             AND ((e.tiktok_url IS NOT NULL AND e.tiktok_url LIKE '%/video/%')
                  OR LOWER(e.media_path) LIKE '%.mp4'
                  OR LOWER(e.media_path) LIKE '%.webm'
                  OR LOWER(e.media_path) LIKE '%.mov')
             AND e.thumb_path IS NOT NULL AND TRIM(e.thumb_path) != ''
             AND e.lat IS NOT NULL AND e.lng IS NOT NULL
             AND NOT (',' || COALESCE(e.tags, '') || ',') LIKE '%,2025,%'
           ORDER BY e.id""").fetchall()
    out, seen_keys = [], set()
    for r in rows:
        d = row_to_dict(r)
        key = ((d.get("title") or "").strip().lower(), d["town_label"])
        if key in seen_keys:
            continue
        seen_keys.add(key)
        d["_state"] = extract_state(d.get("town") or "")
        out.append(d)
    return out


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
    exactly like the Scariest tab rule."""
    with get_conn(DB_PATH) as conn:
        pool = _vt_video_pool(conn)
    by_views = lambda d: (-d["_views"], -d["votes"], d["id"])  # noqa: E731
    tonight = _vt_pick(pool, key=by_views)
    scare_rank = {"extreme": 0, "terrifying": 1, "creepy": 2}
    scary_pool = [d for d in pool if d.get("scare_level") in scare_rank]
    scariest = _vt_pick(
        scary_pool,
        key=lambda d: (scare_rank[d["scare_level"]], -d["_views"],
                       -d["votes"], d["id"]))
    nyc = _vt_pick([d for d in pool if d["_state"] == "NY"], key=by_views)
    nj = _vt_pick([d for d in pool if d["_state"] == "NJ"], key=by_views)
    routes = {"tonight": tonight}
    if len(scariest) >= 6:  # thinner than that isn't a tour — hide the tab
        routes["scariest"] = scariest
    if len(nyc) >= 6:
        routes["nyc"] = nyc
    if len(nj) >= 6:
        routes["nj"] = nj
    if route not in routes:
        route = "tonight"
    is_tv = mode == "tv"
    channel_meta = [
        {"id": "tonight", "label": "Tonight's Tour", "emoji": "🎬",
         "title": "🎬 Tonight's Virtual Tour",
         "sub": "The best video haunts in the country, one after another "
                "— sit back and ride along.",
         "blurb": "Tonight's best video haunts nationwide, ranked by "
                  "what haunters are actually watching."},
        {"id": "scariest", "label": "Scariest in America", "emoji": "😱",
         "title": "😱 Scariest in America — Virtual Tour",
         "sub": "The most terrifying video haunts on the map, ranked by "
                "scare level — enter if you dare.",
         "blurb": "The creepiest, most terrifying video haunts on the "
                  "map, ranked by scare level."},
        {"id": "nyc", "label": "NYC Metro", "emoji": "🗽",
         "title": "🗽 NYC Metro — Virtual Tour",
         "sub": "Video haunts across the five boroughs and Long Island "
                "— the densest haunting in America, one stop at a time.",
         "blurb": "The five boroughs + Long Island: Dyker Heights, "
                  "Staten Island, Lindenhurst and more."},
        {"id": "nj", "label": "New Jersey Haunts", "emoji": "🎃",
         "title": "🎃 New Jersey Haunts — Virtual Tour",
         "sub": "Jersey's best video haunts — Bergen, Essex, Morris and "
                "beyond, ranked by views.",
         "blurb": "Dumont, Hawthorne, Ridgewood, Hackensack — Jersey's "
                  "most-watched video haunts."},
    ]
    channels = [c for c in channel_meta if c["id"] in routes]

    def slim(stops: list[dict]) -> list[dict]:
        return [{
            "id": d["id"], "title": d["title"], "town": d["town"],
            "town_label": d["town_label"], "state": d["_state"],
            "address": d.get("address") or "",
            "lat": d["lat"], "lng": d["lng"],
            "thumb_url": d["thumb_url"], "media_url": d["media_url"],
            "media_type": d["media_type"],
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
    media: UploadFile = File(None),
):
    error: str | None = None
    title, town, display_name = title.strip()[:120], town.strip()[:80], display_name.strip()[:40]
    # address/description must be declared here — FastAPI silently drops
    # undeclared form fields, which is how crew uploads lost them (Oct 2026).
    address = address.strip()[:200]
    description = description.strip()[:1000]
    category = category if category in CATEGORIES else "halloween"
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
    if lat.strip() or lng.strip():
        try:
            lat_f, lng_f = float(lat), float(lng)
            if not (-90 <= lat_f <= 90 and -180 <= lng_f <= 180):
                raise ValueError
        except ValueError:
            error = "Map pin coordinates look invalid — try tapping the map again."

    if not error and not title:
        error = "Please give your haunt a title."
    if not error and not town:
        error = "Please add a town or neighborhood."
    if not error and (not media or not media.filename) and category not in ("events", "halloween_stores", "live"):
        error = "Please attach a photo or video."

    entry_id = None
    has_media = media and media.filename
    if not error:
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
                error = str(e)

    if not error:
        now = datetime.now(timezone.utc).isoformat()
        with get_conn(DB_PATH) as conn:
            for col, ddl in (("uploader_email", "TEXT"),
                             ("notify_votes", "INTEGER DEFAULT 0")):
                try:
                    conn.execute(f"ALTER TABLE entries ADD COLUMN {col} {ddl}")
                except Exception:
                    pass  # column already exists
            cur = conn.execute(
                """INSERT INTO entries
                   (title, town, display_name, media_path, thumb_path, media_type,
                    lat, lng, votes, flagged, hidden, is_sample, category, created_at,
                    scare_level, tags, tiktok_url, uploader_email, notify_votes,
                    address, description)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0, 0, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
                (title, town, display_name or None, media_rel or "", thumb_rel,
                 media_type or "none", lat_f, lng_f, category, now, scare_level, tags,
                 tiktok_url or None, uploader_email or None, notify_votes,
                 address or None, description or None),
            )
            entry_id = cur.lastrowid
            conn.commit()

    if error:
        return templates.TemplateResponse(request, "upload.html", {"request": request, "error": error}, status_code=400
        )
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
    "seconds INTEGER, sid TEXT)"
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


def _log_engagement(event: str, entry_id: int | None = None) -> None:
    """Insert one engagement row. Town is derived server-side from the
    entry (its extract_city_state label). Fire-and-forget: analytics must
    never break the interaction that produced the event."""
    try:
        town = None
        if entry_id:
            with get_conn(DB_PATH) as conn:
                row = conn.execute(
                    "SELECT town FROM entries WHERE id = ?", (entry_id,)).fetchone()
            if row:
                town = extract_city_state(row["town"] or "") or row["town"]
        with get_conn(DB_PATH) as conn:
            conn.execute(ENGAGEMENT_TABLE_SQL)
            conn.execute(
                "INSERT INTO engagement_events (created_at, event, entry_id, town) "
                "VALUES (?, ?, ?, ?)",
                (datetime.now(timezone.utc).isoformat(), event, entry_id, town))
            conn.commit()
    except Exception:
        pass


def _ensure_engagement_columns(conn) -> None:
    """PRAGMA-checked ALTERs adding the Item 6 columns (path / seconds /
    sid) to engagement_events on DBs created before they existed — same
    migration style as the fan_art / entries column additions."""
    cols = {r["name"] for r in conn.execute("PRAGMA table_info(engagement_events)")}
    for col, ddl in (("path", "TEXT"), ("seconds", "INTEGER"), ("sid", "TEXT")):
        if col not in cols:
            conn.execute(f"ALTER TABLE engagement_events ADD COLUMN {col} {ddl}")


def _log_engaged(seconds: int, path: str, sid: str | None) -> None:
    """Insert one engaged-time beacon row: `seconds` of INCREMENTAL engaged
    time (client sends deltas, never cumulative totals) spent on `path`.
    Real time-on-page per page/session is SUM(seconds) over these rows —
    e.g. SELECT path, SUM(seconds) FROM engagement_events
    WHERE event='engaged' GROUP BY path. Fire-and-forget like
    _log_engagement: analytics must never break a page."""
    try:
        with get_conn(DB_PATH) as conn:
            conn.execute(ENGAGEMENT_TABLE_SQL)
            _ensure_engagement_columns(conn)
            conn.execute(
                "INSERT INTO engagement_events (created_at, event, path, seconds, sid) "
                "VALUES (?, ?, ?, ?, ?)",
                (datetime.now(timezone.utc).isoformat(), ENGAGED_EVENT,
                 path, seconds, sid))
            conn.commit()
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
    body {event, entry_id} — or {event:'engaged', seconds, path} for the
    Item 6 time-on-page beacon. navigator.sendBeacon posts as text/plain,
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
            if seconds > 0 and path.startswith("/"):
                _log_engaged(seconds, path, request.cookies.get("hm_sid"))
        elif event in TRACK_EVENTS:
            entry_id = data.get("entry_id")
            try:
                entry_id = int(entry_id) if entry_id is not None else None
            except (TypeError, ValueError):
                entry_id = None
            _log_engagement(event, entry_id)
    except Exception:
        pass
    return Response(status_code=204)


@app.get("/d/{entry_id}", response_class=HTMLResponse)
def detail(request: Request, entry_id: int):
    entry = get_entry(entry_id)
    if not entry or entry["hidden"]:
        raise HTTPException(404, "Entry not found.")
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
    more_haunts = sorted(
        chain["more_near"],
        key=lambda p: (1 if p["id"] in DUEL_EXCLUDE_IDS else 0, p["distance"]),
    )[:3]
    # Collection loop: ids of every visible pin in this pin's town + category,
    # so the page can show "You've seen X of Y displays in [Town]" (the
    # seen-set itself lives in the visitor's localStorage — no accounts).
    entry_label = extract_city_state(entry["town"] or "") or entry["town"] or ""
    with get_conn(DB_PATH) as conn:
        town_rows = conn.execute(
            "SELECT e.*, COALESCE(v.views, 0) AS _views FROM entries e "
            "LEFT JOIN (SELECT CAST(substr(path, 4) AS INTEGER) AS eid, "
            "                  COUNT(*) AS views FROM page_views "
            "                  WHERE path LIKE '/d/%' GROUP BY eid) v "
            "  ON v.eid = e.id "
            "WHERE e.category = ? AND e.hidden = 0",
            (entry["category"],)).fetchall()
    town_pin_ids = []
    town_haunts = []
    for r in town_rows:
        p = row_to_dict(r)
        if (extract_city_state(p["town"] or "") or p["town"] or "") != entry_label:
            continue
        town_pin_ids.append(p["id"])
        if p["id"] != entry_id:
            town_haunts.append(p)
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
         "tips": tips, "scare_counts": scare_counts, "scare_total": scare_total,
         "scare_pick": scare_pick, "next_pin": effective_next_pin,
         "next_geo_pin": geo_next_pin,
         "next_is_video": bool(video_next_pin),
         "video_chain": chain.get("video_chain", []),
         "town_centers": chain.get("town_centers", []),
         "more_videos": chain.get("more_videos", []),
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


@app.get("/leaderboard", response_class=HTMLResponse)
def leaderboard(request: Request, cat: str = "halloween"):
    cat = cat if cat in CATEGORIES else "halloween"
    with get_conn(DB_PATH) as conn:
        # Dan, Oct 23: rank by detail-page views, same logic as the
        # homepage Trending strip — votes aren't flowing yet, so the old
        # votes-first board was effectively newest-first. Revisit votes
        # as a ranking input once they pick up.
        top = [row_to_dict(r) for r in conn.execute(
            "SELECT e.*, COALESCE(v.views, 0) AS _views FROM entries e "
            "LEFT JOIN (SELECT CAST(substr(path, 4) AS INTEGER) AS eid, "
            "                  COUNT(*) AS views FROM page_views "
            "                  WHERE path LIKE '/d/%' GROUP BY eid) v "
            "  ON v.eid = e.id "
            "WHERE e.hidden = 0 AND e.category = ? "
            "ORDER BY _views DESC, e.votes DESC, e.id LIMIT 15",
            (cat,),
        ).fetchall()]
        per_town = []
        for t in towns(cat):
            rows = conn.execute(
                "SELECT * FROM entries WHERE hidden = 0 AND category = ? "
                "AND town = ? ORDER BY votes DESC, created_at DESC LIMIT 3",
                (cat, t),
            ).fetchall()
            per_town.append({"town": t, "entries": [row_to_dict(r) for r in rows]})
    return templates.TemplateResponse(request, "leaderboard.html",
        {"request": request, "top": top, "per_town": per_town,
         "cat": cat, "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI}
    )


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

def _passport_towns(conn) -> list[dict]:
    """[{town, town_label, total, url, slug, ids}] for the passport.

    `ids` rides along beyond the spec'd fields: the progress itself is
    computed client-side from the visitor's seen set, which is a bare
    list of pin ids, so the client needs each town's id list to count
    how many of them were seen. `town` and `town_label` are both the
    canonical extract_city_state label (the key the town feed groups
    by, and the label every card displays)."""
    grouped: dict[str, list[int]] = {}
    for r in conn.execute(
            "SELECT id, town FROM entries "
            "WHERE hidden = 0 AND category = 'halloween' ORDER BY id").fetchall():
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


@app.get("/api/passport-data")
def api_passport_data():
    """Per-town passport denominators + pin ids, as one JSON list.
    Computed per request (a single grouped scan of ~2k halloween rows
    at snapshot scale — cheap); Cache-Control lets browsers / the CDN
    reuse it briefly instead of recomputing on every homepage load,
    since the homepage chip fetches it too."""
    with get_conn(DB_PATH) as conn:
        data = _passport_towns(conn)
    resp = JSONResponse(data)
    resp.headers["Cache-Control"] = "public, max-age=300"
    return resp


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
    return sorted(
        ({"label": l, "slug": _town_slug(l), "count": c} for l, c in counts.items()),
        key=lambda x: x["label"],
    )


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
    with get_conn(DB_PATH) as conn:
        rows = [row_to_dict(r) for r in conn.execute(
            "SELECT * FROM entries WHERE hidden = 0 AND category = 'halloween' "
            "ORDER BY votes DESC, created_at DESC").fetchall()]
    entries = [e for e in rows if e["town_label"] == label]
    # Video-first ranking (engagement, Oct 22): stable sort — footage pins
    # ahead of photo-only pins, votes/newest order kept within each group.
    entries.sort(key=lambda e: 0 if _entry_has_video(e) else 1)
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
    urls = ["/", "/map", "/nearby", "/tour", "/diy", "/diy-costumes", "/games", "/leaderboard",
            "/towns", "/passport", "/daily", "/advertise", "/media-kit", "/about", "/costume-contest", "/trivia", "/haunt-or-not", "/fan-art",
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
                  "Runs through Halloween — and on the Jolly Map through Christmas"]},
    {"id": "premium", "name": "Premium", "price": 500,
     "stripe_link": "https://buy.stripe.com/7sY7sK3K05ySge49iebbG01",
     "blurb": "Homepage plus the weekly email.",
     "features": ["Everything in Featured",
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
    today = datetime.now(timezone.utc).date().isoformat()
    week_ago = (datetime.now(timezone.utc) - timedelta(days=7)).isoformat()
    stats = {"today": 0, "week": 0, "pins": 0, "towns": 0}
    with get_conn(DB_PATH) as conn:
        try:
            stats["today"] = conn.execute(
                "SELECT COUNT(DISTINCT sid) FROM page_views WHERE substr(viewed_at, 1, 10) = ?",
                (today,)).fetchone()[0]
            stats["week"] = conn.execute(
                "SELECT COUNT(DISTINCT sid) FROM page_views WHERE viewed_at >= ?",
                (week_ago,)).fetchone()[0]
        except Exception:
            pass
        stats["pins"] = conn.execute(
            "SELECT COUNT(*) FROM entries WHERE hidden = 0").fetchone()[0]
        sponsors = [dict(r) for r in conn.execute(
            "SELECT * FROM sponsors WHERE is_active = 1 ORDER BY "
            "CASE tier WHEN 'title' THEN 0 WHEN 'premium' THEN 1 ELSE 2 END LIMIT 1").fetchall()]
    with get_conn(DB_PATH) as conn:
        town_rows = conn.execute(
            "SELECT DISTINCT town FROM entries WHERE hidden = 0").fetchall()
    stats["towns"] = len({lbl for r in town_rows
                          if (lbl := extract_city_state(r["town"] or ""))})
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
    ("live", "Live"),
]

MEDIA_KIT_GAMES = ["Haunt or Not", "Scare-O-Meter", "Daily Halloween Trivia", "Costume Contest"]


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
# Top-of-page featured set (Dan, Oct 23): his friends' ZombieSquad mix on
# the Dead On Pictures channel, featured at the top of /music by request.
# Verified via yt-dlp 2026-10-23: public, playable_in_embed, maxres thumb.
MUSIC_SPOTLIGHT = {
    "id": "MlgxFvrCgoA",
    "title": "ZombieSquad EDM Mix Session | 20261023 | EDM - Dance - House",
    "channel": "Dead On Pictures",
    "meta": "Full-length set · 2:13:03",
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
         "yt_spotlight": MUSIC_SPOTLIGHT,
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
    {"title": "Halloweentown", "year": 1998,
     "blurb": "Disney Channel's 1998 original is pure bottled nostalgia — "
              "Grandma Aggie, a giant pumpkin in the town square, and a "
              "town where it's always Halloween.",
     "id": "ozGLDYRjvN0", "channel": "Disney Channel",
     "kind": "Official Clip"},
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


@app.get("/movies", response_class=HTMLResponse)
def movies_page(request: Request):
    return templates.TemplateResponse(
        request, "movies.html",
        {"site_name": SITE_NAME, "new": MOVIE_NEW,
         "classics": MOVIE_CLASSICS, "deep_cuts": MOVIE_DEEP_CUTS},
    )


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
        "total_pins": 0,
        "categories": [],
        "town_count": 0,
        "states": [],
        "games": MEDIA_KIT_GAMES,
    }
    with get_conn(DB_PATH) as conn:
        try:
            kit["visitors_today"] = conn.execute(
                "SELECT COUNT(DISTINCT sid) FROM page_views WHERE substr(viewed_at, 1, 10) = ?",
                (today_d.isoformat(),)).fetchone()[0]
            kit["visitors_week"] = conn.execute(
                "SELECT COUNT(DISTINCT sid) FROM page_views WHERE substr(viewed_at, 1, 10) >= ?",
                (week_start_d.isoformat(),)).fetchone()[0]
        except Exception:
            pass
        counts = {r[0]: r[1] for r in conn.execute(
            "SELECT category, COUNT(*) FROM entries WHERE hidden = 0 GROUP BY category").fetchall()}
        kit["total_pins"] = sum(counts.values())
        kit["categories"] = [
            {"label": label, "count": counts[key]}
            for key, label in MEDIA_KIT_CATEGORY_LABELS if counts.get(key)
        ]
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
    kit["town_count"] = len(labels)
    kit["states"] = sorted(state_set)
    kit["state_count"] = len(state_set - {"DC"})
    kit["has_dc"] = "DC" in state_set
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
    src = (source_url or "").strip()[:300]
    if not (src.startswith("https://") or src.startswith("http://")):
        src = None
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
        # --- engagement events (Wave 2, Item 2): last 7 days ---
        conn.execute(ENGAGEMENT_TABLE_SQL)
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
        engagement = {
            "counts": [(ev, eng_counts[ev]) for ev in ENGAGEMENT_EVENTS_ALL],
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
         "duration": duration, "engagement": engagement})


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


@app.get("/admin/backup")
def admin_backup(request: Request, background: BackgroundTasks):
    """Download a zip of the database + all uploads (for automated backups). Admin only."""
    if not is_admin(request):
        raise HTTPException(401, "Not authorized.")
    tmp = Path(tempfile.mkstemp(prefix="hauntmap-backup-", suffix=".zip")[1])
    try:
        with zipfile.ZipFile(tmp, "w", zipfile.ZIP_DEFLATED) as z:
            if DB_PATH.exists():
                z.write(DB_PATH, "hauntmap.db")
            if UPLOAD_DIR.exists():
                for f in sorted(UPLOAD_DIR.rglob("*")):
                    if f.is_file():
                        z.write(f, f"uploads/{f.relative_to(UPLOAD_DIR)}")
    except Exception:
        tmp.unlink(missing_ok=True)
        raise
    background.add_task(tmp.unlink, True)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%d")
    return FileResponse(tmp, filename=f"hauntmap-backup-{stamp}.zip")


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
        tmp = save_upload(logo, MAX_PHOTO_BYTES)
        try:
            with Image.open(tmp) as im:
                im.verify()
        except (UnidentifiedImageError, OSError):
            tmp.unlink(missing_ok=True)
            raise HTTPException(400, "Not a readable image")
        sponsor_dir = UPLOAD_DIR / "sponsors"
        sponsor_dir.mkdir(exist_ok=True)
        logo_path = f"sponsors/{uuid.uuid4().hex}{ext}"
        shutil.move(tmp, UPLOAD_DIR / logo_path)
        _normalize_orientation(UPLOAD_DIR / logo_path)
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

