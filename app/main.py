"""HauntMap v1 — mobile-first web app for sharing Halloween decorations.

Stack: FastAPI + Jinja2 + SQLite + local disk uploads. No user accounts in v1.
Voting is limited to one vote per browser per entry via cookie — this is a
SOFT limit only (cookies are trivially cleared); it stops casual double
voting, not determined abuse. See the vote route below.
"""
import hashlib
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
    return d


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


def detail_chain(entry: dict) -> dict:
    """Loop data for a detail page: the nearest-pin chain (next + reciprocal
    prev), a 'More near here' rail and a 'More like this' rail, so no detail
    page is ever a dead end. All same-category; distances in miles."""
    peers = category_peers(entry)
    out = {"next_pin": None, "prev_pin": None, "more_near": [], "more_like": []}
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


def _pick_tonights_display(conn, exclude_id=None) -> dict | None:
    """Tonight's Display: a fresh random pick on every homepage load
    (Dan, Oct 22 — supersedes the earlier date-seeded daily pick). Pool
    rules unchanged: eligible halloween pins that have video, plus the
    200 most-viewed eligible pins (by detail-page views), real media
    only. exclude_id (the visitor's previous pick, from the tonight_last
    cookie) is skipped when the pool has more than one entry, so a
    reload doesn't serve the same pin twice in a row."""
    rows = _tonight_pool(conn, "halloween")
    if not rows:
        rows = _tonight_pool(conn, None)
    if not rows:
        return None
    quality = {r["id"]: r for r in rows if r["_has_video"]}
    for r in sorted(rows, key=lambda r: (-r["_views"], r["id"]))[:200]:
        quality.setdefault(r["id"], r)
    pool = [quality[k] for k in sorted(quality)]
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
    if tag in ("animatronics", "inflatables", "handmade", "walkthrough", "projector", "lights", "music", "street-wide", "multi-house", "ticketed", "2025"):
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
        sponsors = [dict(r) for r in conn.execute(
            "SELECT * FROM sponsors WHERE is_active = 1 ORDER BY "
            "CASE tier WHEN 'title' THEN 0 WHEN 'premium' THEN 1 ELSE 2 END, created_at").fetchall()]
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
    tonight_label = today_et.strftime("%A, %B ") + str(today_et.day)
    response = templates.TemplateResponse(request, "index.html",
        {"request": request, "entries": entries, "sort": sort,
         "town": town, "towns": towns(cat, state), "states": states(cat),
         "state": state, "region": region, "voted": voted,
         "cat": cat, "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI,
         "scare": scare, "tag": tag, "video": "1" if video.strip() == "1" else "",
         "tonight": tonight, "tonight_label": tonight_label,
         "sponsors": sponsors,
         "bottom_tabs": _place_tabs(cat, state, region, sort, scare, tag,
                                    "1" if video.strip() == "1" else ""),
         "tier_labels": {"featured": "Featured Sponsor", "premium": "Premium Sponsor", "title": "Title Sponsor"}},
    )
    if tonight:
        response.set_cookie("tonight_last", str(tonight["id"]),
                            max_age=7 * 24 * 3600, path="/", samesite="lax")
    return response


@app.get("/events")
def events_redirect():
    # The header's Events artwork links to /events (Dan, Oct 22); the
    # events view itself is the home feed filtered to the events category.
    return RedirectResponse("/?cat=events", status_code=302)


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
# card. Card art is the site's own stock Halloween imagery, never a creator's
# photo. Every source link was verified live (HTTP 200) on 2026-10-22.

COSTUME_SECTIONS = [
    {
        "id": "kids",
        "title": "&#x1F383; For Kids",
        "sub": "Weekend projects and after-school builds — cardboard, felt and a glue gun go a long way.",
        "ideas": [
            {"name": "Cardboard Robot", "who": "Kids 5–10", "difficulty": "Easy", "time": "About 2 hours",
             "materials": "Two cardboard boxes, foil or silver tape, bottle caps, dryer ducting, glow sticks",
             "blurb": "The classic box robot, upgraded: light-up trim, a LEGO-style control panel and glow-in-the-dark cuffs so your little bot stays visible after dark.",
             "source": "Goodnight Fox", "url": "https://www.goodnightfox.com/blog/robot-costume", "img": "costume_stock_1.jpg"},
            {"name": "Umbrella Jellyfish", "who": "Kids 4+", "difficulty": "Easy", "time": "About 30 minutes",
             "materials": "Clear or white umbrella, bubble wrap, ribbon scraps, light-colored outfit",
             "blurb": "A clear umbrella becomes the jellyfish bell and the ribbons do the floating — a showstopper that weighs almost nothing and needs zero sewing.",
             "source": "PSECU", "url": "https://www.psecu.com/learn/6-easy-diy-halloween-costumes-for-kids", "img": "costume_stock_2.jpg"},
            {"name": "No-Sew Superhero Cape", "who": "Kids 3–8", "difficulty": "Easy", "time": "About 20 minutes",
             "materials": "One oversized T-shirt, fabric markers or felt, scissors",
             "blurb": "One old tee transforms into a cape with its neckline intact — then your kid designs their own hero emblem. Sleeves become matching wristbands.",
             "source": "NOLA Family", "url": "https://nolafamily.com/diy-halloween-costumes-for-kids/", "img": "costume_stock_3.jpg"},
            {"name": "Pineapple Rainsuit Costume", "who": "Toddlers & kids", "difficulty": "Easy", "time": "About 45 minutes",
             "materials": "Yellow rainsuit or sweatsuit, green felt, headband, toilet paper roll, hot glue",
             "blurb": "A yellow outfit plus a felt pineapple crown — and because the base is rain gear, a drizzly Halloween night can't ruin it.",
             "source": "Jan & Jul", "url": "https://janandjul.com/easy-halloween-costumes/", "img": "costume_stock_4.jpg"},
            {"name": "Spooky Paper Mask", "who": "Kids 6+", "difficulty": "Medium", "time": "An afternoon (with drying time)",
             "materials": "Tissue box cardboard, kitchen paper, glue, dyes or paint, elastic, coloring pens",
             "blurb": "A build-it-from-scratch mask project: shape the base from a flattened box, then finish it as a pumpkin, a mummy, or a flower-crowned spooky face.",
             "source": "Cushelle", "url": "https://www.cushelle.com/everyday-fun/craft-ideas/3-seriously-spooky-diy-kids-halloween-costume-ideas/", "img": "costume_stock_5.jpg"},
            {"name": "Baby Lamb (Cotton-Ball Wool)", "who": "Babies & toddlers", "difficulty": "Easy", "time": "About 30 minutes",
             "materials": "Black onesie and hat, cotton balls, black felt, hot glue",
             "blurb": "The softest costume on this page: cotton balls glued over a black onesie make instant wool, and floppy felt ears finish the flock.",
             "source": "Sustainably Kind Living", "url": "https://sustainablykindliving.com/diy-halloween-costumes/", "img": "costume_stock_6.jpg"},
        ],
    },
    {
        "id": "adults",
        "title": "&#x1F9DB; For Adults",
        "sub": "Closet-first costumes and pun costumes that land at the party — most start with clothes you already own.",
        "ideas": [
            {"name": "Wednesday Addams", "who": "Adults & teens", "difficulty": "Easy", "time": "Under 1 hour",
             "materials": "Black dress with white collar (or layered shirt), pale makeup, black eyeliner, braids or a wig",
             "blurb": "Deadpan is the whole costume: pale base, a widow's-peak eyeliner flick, two braids, and your most miserable expression.",
             "source": "Slap Dash Mom", "url": "https://slapdashmom.com/wednesday-addams-costume-tutorial/", "img": "costume_stock_7.jpg"},
            {"name": "Cereal Killer", "who": "Adults", "difficulty": "Easy", "time": "About 1 hour",
             "materials": "White tee, mini cereal boxes, cardboard knives, red paint, duct tape, marker",
             "blurb": "The pun costume that never dies: cereal boxes and cardboard cutlery taped to a tee, finished with a tasteful amount of 'blood' splatter.",
             "source": "Marc and Mandy", "url": "https://marcandmandy.com/easy-cheap-diy-halloween-costumes/", "img": "costume_stock_8.jpg"},
            {"name": "It's Raining Men", "who": "Adults", "difficulty": "Easy", "time": "About 30 minutes",
             "materials": "Cheap umbrella, string, safety pins, printed photos of your favorite leading men",
             "blurb": "Hallelujah — photos dangling from an umbrella on strings. Absurd, cheap, and it photographs like a dream.",
             "source": "Goemans Appliances Blog", "url": "https://blog.goemans.com/easy-diy-halloween-costumes", "img": "costume_stock_1.jpg"},
            {"name": "Mad Scientist", "who": "Adults", "difficulty": "Easy", "time": "About 30 minutes",
             "materials": "Lab coat or white shirt, wild hair (backcombing or a wig), plastic bottle 'concoction', face paint",
             "blurb": "Teased-up hair, a lab coat and a glowing mystery potion in a bottle. The cackle is up to you.",
             "source": "The Life Planner", "url": "https://thelifeplanner.co/blog/post/10_diy_halloween_costumes_you_can_make_last_minute.html", "img": "costume_stock_2.jpg"},
            {"name": "Rosie the Riveter", "who": "Adults", "difficulty": "Easy", "time": "About 15 minutes",
             "materials": "Chambray or denim shirt, red bandana, red lipstick, rolled-up sleeves",
             "blurb": "Two thrift-store staples and the most famous bandana in history. Flex mandatory, sewing nonexistent.",
             "source": "VOA Ohio & Indiana", "url": "https://www.voaohin.org/5-last-minute-classic-diy-halloween-costumes/", "img": "costume_stock_3.jpg"},
            {"name": "Beetlejuice (Tape-Striped Suit)", "who": "Adults", "difficulty": "Medium", "time": "About 1–2 hours",
             "materials": "Old blazer and trousers, black electrical tape, baby powder for hair, green eyeshadow",
             "blurb": "No striped suit? Make one: electrical-tape stripes on a thrifted blazer, powdered messy hair, and a little mossy green shading.",
             "source": "London Mums Magazine", "url": "https://www.londonmumsmagazine.com/whats-on/activities/get-creative/simple-homemade-halloween-outfits-hairdos-on-a-budget/", "img": "costume_stock_4.jpg"},
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
             "source": "Journey With J", "url": "https://www.journeywithjblog.com/harry-hermione-diy-halloween-costumes/", "img": "costume_stock_5.jpg"},
            {"name": "Scarecrow Couple", "who": "Couples & families", "difficulty": "Easy", "time": "About 1–2 hours",
             "materials": "Flannel shirts, jeans or a dress, raffia or straw, burlap patches, straw hats, rope belt",
             "blurb": "Cozy fall energy for two: patched flannel, raffia 'straw' at the cuffs, and a sunflower or faux-corn prop to sell the harvest look.",
             "source": "Simple Made Pretty", "url": "https://simplemadepretty.com/halloween-couples-costumes/", "img": "costume_stock_6.jpg"},
            {"name": "Giant Waffle & Eleven", "who": "Couples, siblings, parent + kid", "difficulty": "Medium", "time": "An afternoon",
             "materials": "Cardboard, yellow paint, yellow pool noodle, straps, red foam sheet",
             "blurb": "One of you is a giant Eggo — pool-noodle strips make the waffle grid — and the other just needs a pink dress and a box of the real thing.",
             "source": "See Kate Sew", "url": "https://seekatesew.com/how-to-make-a-waffle-costume-diy-eggo-costume/", "img": "costume_stock_7.jpg"},
            {"name": "Matching Mimes", "who": "Couples & groups", "difficulty": "Easy", "time": "About 30 minutes",
             "materials": "Striped shirts, black pants, suspenders, berets, white gloves, white face paint",
             "blurb": "Identical stripes, silent all night. The easiest group costume ever — and the invisible box bit never gets old.",
             "source": "Urban Mamaz", "url": "https://urbanmamaz.com/easy-diy-halloween-costumes-for-couples-that-totally-match-the-vibe/", "img": "costume_stock_8.jpg"},
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
             "source": "DIY Joy", "url": "https://diyjoy.com/easy-diy-halloween-costume-ideas/", "img": "costume_stock_1.jpg"},
            {"name": "No-Sew Airheads Candy", "who": "Kids", "difficulty": "Easy", "time": "About 1 hour",
             "materials": "Neon sweatsuit, red/white/black felt, hot glue, printed letter template",
             "blurb": "A sweatsuit plus felt logos becomes a walking candy wrapper — bright, warm, and comfy enough to run house-to-house all night.",
             "source": "Jenn Hallak", "url": "https://jennhallak.com/blog/diy-airheads-costume", "img": "costume_stock_2.jpg"},
            {"name": "15-Minute Closet Costumes", "who": "Adults", "difficulty": "Easy", "time": "5–15 minutes",
             "materials": "Whatever is already in your closet: flannel, overalls, a suit, a black dress — plus one cheap add-on each",
             "blurb": "Work backwards from your wardrobe: overalls plus a red tee is a plumber, a suit plus sunglasses is an agent, flannel plus raffia is a scarecrow.",
             "source": "Bee Bulletin", "url": "https://beebulletin.com/last-minute-halloween-costumes/", "img": "costume_stock_3.jpg"},
            {"name": "Bubble Bath", "who": "Kids", "difficulty": "Easy", "time": "About 20 minutes",
             "materials": "White outfit, white balloons, safety pins, shower cap, rubber duck",
             "blurb": "Pin clusters of white balloons onto a white outfit and you are a walking bubble bath. The duck is not optional — it's the whole joke.",
             "source": "Town & Style", "url": "https://townandstyle.com/last-minute-halloween-costume-diys/", "img": "costume_stock_4.jpg"},
        ],
    },
    {
        "id": "scary",
        "title": "&#x1F9DF; Scary & Makeup-Led",
        "sub": "The costume is the makeup: wounds, bites and face paint that do the heavy lifting.",
        "ideas": [
            {"name": "Zombie Bite Wound", "who": "Adults & teens", "difficulty": "Medium", "time": "About 30–45 minutes",
             "materials": "Scar putty or liquid latex, face powder, red and burgundy paint, fake blood, cotton swabs",
             "blurb": "A ring of scar putty, teeth marks pressed in with a spoon handle, and layered reds — a bite wound that looks fresh off the horde.",
             "source": "Insomniac Magazine", "url": "https://www.insomniac.com/magazine/diy-zombie-look/", "img": "costume_stock_5.jpg"},
            {"name": "Open Wound from Glue & Tissue", "who": "Adults & teens", "difficulty": "Medium", "time": "About 45 minutes (with drying)",
             "materials": "PVA glue, toilet tissue, foundation, black eyeshadow, stage blood (fresh + congealed)",
             "blurb": "No latex kit needed: layered tissue and glue become torn skin you can open up, shade, and fill with blood. Genuinely gruesome.",
             "source": "Our Family Life", "url": "https://www.ourfamilylife.co.uk/working-mums-blog/halloween-zombie-make-up", "img": "costume_stock_6.jpg"},
            {"name": "Vampire Makeup", "who": "Adults & teens", "difficulty": "Easy", "time": "About 30 minutes",
             "materials": "Pale foundation or white face paint, dark eyeshadow, red lipstick, fangs, fake blood",
             "blurb": "Porcelain-pale skin, shadow-hollowed eyes and one perfect blood drip at the mouth — the eternal Halloween aristocrat.",
             "source": "Halloween Junkie", "url": "https://halloween-junkie.com/tag/tutorials/", "img": "costume_stock_7.jpg"},
            {"name": "Sugar Skull (Calavera) Face Paint", "who": "Adults & older kids", "difficulty": "Medium", "time": "About 1 hour",
             "materials": "White, black and bright face paints, fine brush, faux roses, lace, headband, hot glue",
             "blurb": "A white base, petal-ringed eyes and fine black detail work, crowned with a handmade rose-and-lace headpiece. Dramatic but forgiving — you can always repaint.",
             "source": "Cuckoo4Design", "url": "https://cuckoo4design.com/fright-tastic-halloween-home-tour/", "img": "costume_stock_8.jpg"},
        ],
    },
]


@app.get("/diy-costumes", response_class=HTMLResponse)
def diy_costumes_page(request: Request):
    return templates.TemplateResponse(
        request, "diy_costumes.html", {"sections": COSTUME_SECTIONS},
    )


# ------------------------------------------------------------- haunt or not

DUEL_EXCLUDE_IDS = frozenset({824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 924, 925, 926, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1273, 1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2064, 2073, 2081, 2082, 2084, 2094, 2098, 2100, 2101, 2104, 2106, 2107, 2108, 2109, 2110, 2112, 2119, 2120, 2121, 2122, 2126, 2127, 2130, 2131, 2133, 2134, 2135, 2136, 2137, 2140, 2142, 2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2155, 2156, 2160, 2162, 2168, 2169, 2170, 2172, 2174, 2178, 2179, 2181, 2182, 2186, 2193, 2199, 2202, 2204, 2205, 2206, 2208, 2209, 2211, 2214, 2217, 2221, 2226, 2227, 2228, 2230, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239, 2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2251, 2252, 2253, 2254, 2255, 2256, 2257, 2258, 2259, 2260, 2261, 2262, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271, 2272, 2273, 2274, 2275, 2276, 2277, 2280, 2284, 2288, 2291, 2292, 2293, 2294, 2295, 2296, 2300, 2302, 2311, 2312, 2313, 2315, 2320, 2321, 2322, 2323, 2324, 2327, 2328, 2329, 2330, 2332, 2333, 2334, 2335, 2336, 2337, 2338, 2340, 2341, 2343, 2347, 2348, 2350, 2352, 2359, 2363, 2364, 2365, 2366, 2367, 2368, 2369, 2371, 2374, 2375, 2376, 2377, 2379, 2380, 2381, 2386, 2389, 2397, 2398, 2399, 2404, 2405, 2406, 2412, 2417, 2418, 2420, 2421, 2422, 2423, 2431, 2432, 2438, 2440, 2441, 2443, 2444, 2446, 2449, 2450, 2455, 2457, 2460, 2463, 2465, 2470, 2475, 2476, 2478, 2479, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2490, 2491, 2492, 2493, 2494, 2495, 2497, 2498, 2499, 2500, 2501, 2502, 2505, 2506, 2507, 2508, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2531, 2533, 2534, 2537, 2539, 2540, 2541, 2542, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559, 2560, 2561, 2562, 2563, 2564, 2575, 2576, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2585, 2586, 2587, 2588, 2590, 2591, 2592, 2593, 2594, 2595, 2596, 2597, 2598, 2599, 2600, 2601, 2602, 2603, 2604, 2605, 2606, 2609, 2610, 2611, 2612, 2613, 2614, 2615, 2616, 2617, 2618, 2619, 2620, 2621, 2622, 2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630, 2631, 2632, 2635, 2636, 2637, 2638, 2639, 2640, 2644, 2646, 2649, 2656, 2659, 2662, 2668, 2669, 2670, 2671, 2673, 2674, 2675, 2676, 2677, 2678, 2679, 2680, 2681, 2682, 2684, 2686, 2687, 2688, 2691, 2694, 2695, 2699, 2700, 2701, 2702, 2703, 2704, 2705, 2707, 2708, 2709, 2710, 2711, 2712, 2715, 2716, 2717, 2718, 2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2746, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767, 2770, 2771, 2772, 2773, 2774, 2777, 2778, 2779, 2782, 2783, 2784, 2786, 2787, 2788, 2790, 2794, 2795, 2796, 2797, 2798, 2799, 2801, 2802, 2803, 2805, 2807, 2811, 2812, 2813, 2814, 2819, 2820, 2821, 2822, 2823, 2824, 2825, 2826, 2828, 2832, 2833, 2834, 2835, 2836, 2837, 2839, 2842, 2843, 2845, 2847, 2848, 2854, 2855, 2856, 2857, 2860, 2862, 2863, 2864, 2866, 2870, 2871, 2872, 2874, 2876, 2877, 2879, 2880, 2881, 2886, 2888, 2889, 2890, 2891, 2893, 2894, 2896, 2898, 2900, 2901, 2902, 2905, 2907, 2908, 2909, 2910, 2911, 2912, 2914, 2915, 2916, 2919, 2920, 2921, 2922, 2923, 2924, 2925, 2926, 2927, 2928, 2929, 2931, 2932, 2933, 2934, 2935, 2937, 2938, 2939, 2940, 2941, 2946, 2947, 2948, 2949, 2950, 2951, 2952, 2953, 2954, 2955, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2964, 2965, 2968, 2969, 2970, 2974, 2975, 2976, 2978, 2979, 2980, 2981, 2982, 2983, 2986, 2987, 2988, 2989, 2991, 2992, 2998, 2999, 3000, 3003, 3004, 3006, 3007, 3009, 3010, 3011, 3013, 3014, 3015, 3016, 3017, 3019, 3020, 3025, 3026, 3034, 3035, 3036, 3039, 3041, 3042, 3043, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3057, 3058, 3059, 3060, 3061, 3062, 3066, 3067, 3068, 3069, 3070, 3071, 3072, 3073, 3074, 3076, 3077, 3082, 3083, 3085, 3086, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3108, 3109, 3110, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3132, 3134, 3135, 3137, 3138, 3139, 3144, 3145, 3146, 3147, 3148, 3149, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3161, 3162, 3163, 3164, 3165, 3169, 3170, 3171, 3172, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3186, 3188, 3189, 3190, 3191, 3192, 3195, 3196, 3197, 3202, 3203, 3210, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3223, 3224, 3225, 3226, 3227, 3228, 3229, 3230, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3240, 3241, 3242, 3243, 3244, 3245, 3246, 3247, 3248, 3254, 3256, 3257, 3258, 3260, 3261, 3266, 3268, 3269, 3270, 3271, 3272, 3273, 3274, 3275, 3278, 3279, 3280, 3282, 3283, 3288, 3289, 3290, 3291, 3292, 3293, 3295, 3297, 3299, 3300, 3301, 3302, 3303, 3304, 3305, 3312, 3314, 3319, 3320, 3324, 3325, 3326, 3327, 3332, 3333, 3334, 3336, 3337, 3338, 3340, 3343, 3346, 3348, 3352, 3353, 3354, 3355, 3356, 3357, 3359, 3360, 3361, 3362, 3364, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3379, 3380, 3382, 3385, 3387, 3388, 3390, 3391, 3394, 3397, 3398, 3402, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423, 3424, 3427, 3428, 3429, 3432, 3435, 3438, 3439, 3443, 3444, 3445, 3447, 3449, 3450, 3451, 3453, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3466, 3474, 3477, 3482, 3484, 3485, 3489, 3490, 3492, 3497, 3498, 3500, 3501, 3502, 3504, 3506, 3511, 3512, 3513, 3514, 3515, 3516, 3517, 3518, 3521, 3522, 3523, 3524, 3527, 3529, 3531, 3532, 3537, 3540, 3545, 3546, 3548, 3551, 3552, 3554, 3555, 3556, 3559, 3568, 3570, 3571, 3572, 3573})  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)  # stock-photo pins stay out of Haunt or Not (authenticity rule)

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


@app.get("/trivia", response_class=HTMLResponse)
def trivia_page(request: Request):
    today = datetime.now(timezone.utc).date()
    rng = random.Random(today.toordinal())
    picks = rng.sample(TRIVIA_QUESTIONS, 5)
    quiz = []
    for i, item in enumerate(picks):
        order = list(range(4))
        random.Random(today.toordinal() * 10 + i).shuffle(order)
        quiz.append({
            "q": item["q"],
            "options": [item["options"][j] for j in order],
            "answer": order.index(item["answer"]),
        })
    return templates.TemplateResponse(
        request, "trivia.html", {"quiz": quiz, "today_label": today.strftime("%A, %B %-d")},
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


@app.get("/watch", response_class=HTMLResponse)
def watch_page(request: Request):
    """Vertical feed of every pin with actual footage — same predicate as the
    feed's 'Has video' filter: a TikTok /video/ URL or an uploaded video file.
    Pool is the top footage by votes; the ORDER is shuffled per request
    (Dan, Oct 21) so every visit to /watch starts somewhere new."""
    with get_conn(DB_PATH) as conn:
        rows = conn.execute(
            "SELECT * FROM entries WHERE hidden = 0 AND ("
            "(tiktok_url IS NOT NULL AND tiktok_url LIKE '%/video/%')"
            " OR LOWER(media_path) LIKE '%.mp4'"
            " OR LOWER(media_path) LIKE '%.webm'"
            " OR LOWER(media_path) LIKE '%.mov')"
            " ORDER BY votes DESC, created_at DESC LIMIT 60").fetchall()
    entries = [row_to_dict(r) for r in rows]
    random.shuffle(entries)
    return templates.TemplateResponse(request, "watch.html",
        {"request": request, "entries": entries})


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
    uploader_email: str = Form(""),
    media: UploadFile = File(None),
):
    error: str | None = None
    title, town, display_name = title.strip()[:120], town.strip()[:80], display_name.strip()[:40]
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
                                     "multi-house", "ticketed", "2025")})) or None

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
                    scare_level, tags, tiktok_url, uploader_email, notify_votes)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0, 0, ?, ?, ?, ?, ?, ?, ?)""",
                (title, town, display_name or None, media_rel or "", thumb_rel,
                 media_type or "none", lat_f, lng_f, category, now, scare_level, tags,
                 tiktok_url or None, uploader_email or None, notify_votes),
            )
            entry_id = cur.lastrowid
            conn.commit()

    if error:
        return templates.TemplateResponse(request, "upload.html", {"request": request, "error": error}, status_code=400
        )
    return RedirectResponse(f"/d/{entry_id}", status_code=303)


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
    for p in town_haunts:
        p.pop("_views", None)
    return templates.TemplateResponse(request, "detail.html",
        {"request": request, "entry": entry, "voted": voted, "reported": reported,
         "tips": tips, "scare_counts": scare_counts, "scare_total": scare_total,
         "scare_pick": scare_pick, "next_pin": chain["next_pin"],
         "prev_pin": chain["prev_pin"], "more_near": chain["more_near"],
         "more_like": chain["more_like"], "town_pin_ids": town_pin_ids,
         "more_haunts": more_haunts, "town_haunts": town_haunts},
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
    resp = RedirectResponse(f"/d/{entry_id}#scare", status_code=303)
    if old != level:
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
    return RedirectResponse(f"/d/{entry_id}#tips", status_code=303)


@app.post("/d/{entry_id}/vote")
def vote(entry_id: int, request: Request):
    entry = get_entry(entry_id)
    if not entry or entry["hidden"]:
        raise HTTPException(404, "Entry not found.")
    resp = RedirectResponse(f"/d/{entry_id}", status_code=303)
    cookie = f"voted_{entry_id}"
    # Soft limit: one vote per browser. Clearing cookies bypasses it — by design
    # for v1 (no accounts). Good enough to stop casual double-voting.
    if cookie not in request.cookies:
        with get_conn(DB_PATH) as conn:
            conn.execute("UPDATE entries SET votes = votes + 1 WHERE id = ?", (entry_id,))
            conn.commit()
        resp.set_cookie(cookie, "1", max_age=365 * 24 * 3600, httponly=True, samesite="lax")
    return resp


@app.post("/d/{entry_id}/unvote")
def unvote(entry_id: int, request: Request):
    entry = get_entry(entry_id)
    if not entry or entry["hidden"]:
        raise HTTPException(404, "Entry not found.")
    resp = RedirectResponse(f"/d/{entry_id}", status_code=303)
    cookie = f"voted_{entry_id}"
    if cookie in request.cookies:
        with get_conn(DB_PATH) as conn:
            conn.execute("UPDATE entries SET votes = MAX(0, votes - 1) WHERE id = ?", (entry_id,))
            conn.commit()
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


@app.get("/leaderboard", response_class=HTMLResponse)
def leaderboard(request: Request, cat: str = "halloween"):
    cat = cat if cat in CATEGORIES else "halloween"
    with get_conn(DB_PATH) as conn:
        top = [row_to_dict(r) for r in conn.execute(
            "SELECT * FROM entries WHERE hidden = 0 AND category = ? "
            "ORDER BY votes DESC, created_at DESC LIMIT 10",
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
    return templates.TemplateResponse(
        request, "town.html",
        {"label": label, "entries": entries, "site_name": SITE_NAME},
    )


@app.get("/sitemap.xml")
def sitemap():
    base = "https://gethauntmap.com"
    urls = ["/", "/map", "/nearby", "/tour", "/diy", "/diy-costumes", "/games", "/leaderboard",
            "/towns", "/advertise", "/media-kit", "/costume-contest", "/trivia", "/haunt-or-not", "/fan-art",
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
    with get_conn(DB_PATH) as conn:
        conn.execute(FANART_SQL)
        conn.execute(
            "INSERT INTO fan_art (title, artist, town, media_path, thumb_path, votes, approved, created_at) "
            "VALUES (?, ?, ?, ?, ?, 0, 0, ?)",
            (title.strip()[:120], (artist or "").strip()[:60] or None,
             (town or "").strip()[:80] or None, media_rel, thumb_rel,
             datetime.now(timezone.utc).isoformat()),
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
        conn.execute("UPDATE fan_art SET approved = 1 WHERE id = ?", (fid,))
    return RedirectResponse("/admin", status_code=303)


@app.post("/admin/fan-art/{fid}/delete")
def admin_fanart_delete(fid: int, request: Request):
    if not is_admin(request):
        return RedirectResponse("/admin", status_code=303)
    with get_conn(DB_PATH) as conn:
        conn.execute(FANART_SQL)
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
         "duration": duration})


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
                                     "multi-house", "ticketed", "2025")})) or None
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
    """Update title, town label and/or verified street address (admin).

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

