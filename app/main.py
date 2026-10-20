"""HauntMap v1 — mobile-first web app for sharing Halloween decorations.

Stack: FastAPI + Jinja2 + SQLite + local disk uploads. No user accounts in v1.
Voting is limited to one vote per browser per entry via cookie — this is a
SOFT limit only (cookies are trivially cleared); it stops casual double
voting, not determined abuse. See the vote route below.
"""
import hashlib
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
import json
import urllib.request
import urllib.parse
from datetime import datetime, timedelta, timezone
from pathlib import Path

from fastapi import BackgroundTasks, FastAPI, Form, HTTPException, Request, UploadFile, File
from fastapi.responses import FileResponse, HTMLResponse, JSONResponse, RedirectResponse
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from PIL import Image, UnidentifiedImageError

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

CATEGORIES = ("halloween", "christmas", "halloween_stores", "restaurants", "coffee", "shops", "parks", "haunted_houses", "events", "live")
CAT_LABELS = {"halloween": "Halloween", "christmas": "Christmas",
              "halloween_stores": "Halloween Stores",
              "restaurants": "Restaurants", "coffee": "Coffee & Cafes",
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
    return city


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


def make_thumb(src: Path, dest_name: str) -> str:
    """Create a JPEG thumbnail for a photo. Returns the relative thumb path."""
    rel = f"thumbs/{dest_name}_thumb.jpg"
    dest = THUMB_DIR / f"{dest_name}_thumb.jpg"
    with Image.open(src) as im:
        im = im.convert("RGB")
        if im.width > THUMB_MAX_WIDTH:
            im = im.resize(
                (THUMB_MAX_WIDTH, int(im.height * THUMB_MAX_WIDTH / im.width)),
                Image.LANCZOS,
            )
        im.save(dest, "JPEG", quality=80)
    return rel


def make_video_poster(src: Path, dest_name: str) -> str | None:
    """Extract a poster frame from a video for feed thumbnails.
    Returns the relative thumb path, or None if ffmpeg is unavailable/fails."""
    rel = f"thumbs/{dest_name}_poster.jpg"
    dest = THUMB_DIR / f"{dest_name}_poster.jpg"
    try:
        subprocess.run(
            ["ffmpeg", "-y", "-i", str(src), "-ss", "1", "-vframes", "1",
             "-vf", f"scale={THUMB_MAX_WIDTH}:-1", str(dest)],
            capture_output=True, timeout=30, check=True,
        )
        return rel
    except (subprocess.SubprocessError, OSError):
        return None


# ---------------------------------------------------------------- public pages

@app.get("/", response_class=HTMLResponse)
def home(request: Request, sort: str = "top", town: str = "", town_search: str = "",
         state: str = "", region: str = "", cat: str = "halloween", scare: str = "", tag: str = ""):
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
        query += " AND LOWER(town) LIKE ?"
        params.append(f"%{city_part.lower()}%")
        if st_part:
            query += (" AND (LOWER(town) LIKE ? OR LOWER(town) LIKE ?"
                      " OR LOWER(town) LIKE ? OR LOWER(town) LIKE ?)")
            s = st_part.lower()
            params += [f"%, {s} %", f"%, {s}", f"%,{s} %", f"%,{s}"]
    elif region in ("boston", "dc-area"):
        metro_map = {
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
        terms = metro_map[region]
        placeholders = " OR ".join(["LOWER(town) LIKE ?"] * len(terms))
        query += f" AND ({placeholders})"
        params.extend([f"%{t}%" for t in terms])
    elif region in ("staten-island", "brooklyn", "manhattan", "queens", "bronx"):
        borough_map = {
            "staten-island": ["staten island"],
            "brooklyn": ["brooklyn"],
            "manhattan": ["manhattan", "new york, ny"],
            "queens": ["queens"],
            "bronx": ["bronx"],
        }
        borough_terms = borough_map[region]
        placeholders = " OR ".join(["LOWER(town) LIKE ?"] * len(borough_terms))
        query += f" AND ({placeholders})"
        params.extend([f"%{t}%" for t in borough_terms])
    elif region == "long-island":
        li_towns = ["wantagh", "bellmore", "merrick", "levittown", "east meadow", "malverne",
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
    query += f" ORDER BY {order} LIMIT 100"
    with get_conn(DB_PATH) as conn:
        entries = [row_to_dict(r) for r in conn.execute(query, params).fetchall()]
        sponsors = [dict(r) for r in conn.execute(
            "SELECT * FROM sponsors WHERE is_active = 1 ORDER BY "
            "CASE tier WHEN 'title' THEN 0 WHEN 'premium' THEN 1 ELSE 2 END, created_at").fetchall()]
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    return templates.TemplateResponse(request, "index.html",
        {"request": request, "entries": entries, "sort": sort,
         "town": town, "towns": towns(cat, state), "states": states(cat),
         "state": state, "region": region, "voted": voted,
         "cat": cat, "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI,
         "scare": scare, "tag": tag, "sponsors": sponsors,
         "tier_labels": {"featured": "Featured Sponsor", "premium": "Premium Sponsor", "title": "Title Sponsor"}},
    )


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


@app.get("/diy", response_class=HTMLResponse)
def diy_page(request: Request):
    return templates.TemplateResponse(
        request, "diy.html", {"videos": DIY_VIDEOS},
    )


# ------------------------------------------------------------- haunt or not

DUEL_EXCLUDE_IDS = frozenset({824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 924, 925, 926, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156})  # stock-photo pins stay out of Haunt or Not (authenticity rule)

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
    media: UploadFile = File(None),
):
    error: str | None = None
    title, town, display_name = title.strip()[:120], town.strip()[:80], display_name.strip()[:40]
    category = category if category in CATEGORIES else "halloween"
    scare_level = scare_level if scare_level in ("family", "spooky", "creepy", "terrifying", "extreme") else None
    # tags come as repeated form fields from checkboxes
    form = await request.form()
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
            cur = conn.execute(
                """INSERT INTO entries
                   (title, town, display_name, media_path, thumb_path, media_type,
                    lat, lng, votes, flagged, hidden, is_sample, category, created_at,
                    scare_level, tags, tiktok_url)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0, 0, ?, ?, ?, ?, ?)""",
                (title, town, display_name or None, media_rel or "", thumb_rel,
                 media_type or "none", lat_f, lng_f, category, now, scare_level, tags,
                 tiktok_url or None),
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
    return templates.TemplateResponse(request, "detail.html",
        {"request": request, "entry": entry, "voted": voted, "reported": reported,
         "tips": tips, "scare_counts": scare_counts, "scare_total": scare_total,
         "scare_pick": scare_pick},
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
    error = None
    success = False
    if not email or "@" not in email or "." not in email.split("@")[-1]:
        error = "Please enter a valid email address."
    else:
        try:
            with get_conn(DB_PATH) as conn:
                conn.execute(
                    "INSERT INTO subscribers (email, location, created_at) VALUES (?, ?, ?)",
                    (email, location, datetime.now(timezone.utc).isoformat()),
                )
                conn.commit()
            success = True
            # Also add to Mailchimp
            mc_key = os.environ.get("MAILCHIMP_API_KEY")
            mc_list = os.environ.get("MAILCHIMP_AUDIENCE_ID")
            if mc_key and mc_list:
                try:
                    dc = mc_key.split("-")[-1]
                    import hashlib
                    sub_hash = hashlib.md5(email.encode()).hexdigest()
                    url = f"https://{dc}.api.mailchimp.com/3.0/lists/{mc_list}/members/{sub_hash}"
                    resp = requests.put(url,
                        auth=("anystring", mc_key),
                        json={"email_address": email, "status": "subscribed",
                              "merge_fields": {"LOCATION": location}},
                        timeout=10)
                except Exception:
                    pass  # local DB is source of truth; Mailchimp is best-effort
        except sqlite3.IntegrityError:
            # already subscribed — treat as success
            success = True
    # redirect back with a flag
    ref = request.headers.get("referer", "/")
    sep = "&" if "?" in ref else "?"
    return RedirectResponse(f"{ref}{sep}subscribed=1" if success else f"{ref}{sep}sub_error=1",
                            status_code=303)


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
    return templates.TemplateResponse(request, "admin.html",
        {"request": request, "logged_in": True, "flagged": flagged,
         "all_entries": all_entries, "subs": subs, "sub_count": sub_count, "error": None},
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
