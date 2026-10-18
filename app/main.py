"""HauntMap v1 — mobile-first web app for sharing Halloween decorations.

Stack: FastAPI + Jinja2 + SQLite + local disk uploads. No user accounts in v1.
Voting is limited to one vote per browser per entry via cookie — this is a
SOFT limit only (cookies are trivially cleared); it stops casual double
voting, not determined abuse. See the vote route below.
"""
import os
import secrets
import shutil
import sqlite3
import subprocess
import tempfile
import uuid
import zipfile
import math
import json
import urllib.request
import urllib.parse
from datetime import datetime, timezone
from pathlib import Path

from fastapi import BackgroundTasks, FastAPI, Form, HTTPException, Request, UploadFile, File
from fastapi.responses import FileResponse, HTMLResponse, RedirectResponse
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

CATEGORIES = ("halloween", "christmas", "halloween_stores", "restaurants", "coffee", "shops", "parks")
CAT_LABELS = {"halloween": "Halloween", "christmas": "Christmas",
              "halloween_stores": "Halloween Stores",
              "restaurants": "Restaurants", "coffee": "Coffee & Cafes",
              "shops": "Shops", "parks": "Parks"}
CAT_EMOJI = {"halloween": "🎃", "christmas": "🎄", "halloween_stores": "👻",
             "restaurants": "🍽️", "coffee": "☕", "shops": "🛍️", "parks": "🌳"}

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
                        for col in ("referrer", "device"):
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
                        conn.execute(
                            "INSERT INTO page_views (path, viewed_at, referrer, device) VALUES (?, ?, ?, ?)",
                            (path, datetime.now(timezone.utc).isoformat(), referrer, device),
                        )
                        conn.commit()
    except Exception:
        pass  # never break a page load for analytics
    return response


# ---------------------------------------------------------------- helpers

def row_to_dict(row: sqlite3.Row) -> dict:
    d = dict(row)
    d["media_url"] = f"/media/{d['media_path']}"
    d["thumb_url"] = f"/media/{d['thumb_path']}" if d["thumb_path"] else d["media_url"]
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


def extract_city(town: str) -> str:
    """Extract clean city name from a town field like '22 Collins St, Cranford, NJ'."""
    parts = [p.strip() for p in town.split(",") if p.strip()]
    if len(parts) >= 3:
        return parts[-2]  # 'Cranford' from '22 Collins St, Cranford, NJ'
    if len(parts) == 2:
        # 'Hoboken, NJ' -> 'Hoboken'; 'E 69th St, New York' -> 'New York'
        return parts[0] if len(parts[1]) <= 3 else parts[1]
    return parts[0] if parts else town


def extract_city_state(town: str) -> str:
    """Extract 'City, ST' from a town field like '22 Collins St, Cranford, NJ'."""
    parts = [p.strip() for p in town.split(",") if p.strip()]
    if len(parts) >= 2:
        state = parts[-1]
        city = extract_city(town)
        # only append state if it looks like a state (short) and differs from city
        if len(state) <= 3 and state.upper() != city.upper():
            return f"{city}, {state.upper()}"
        return city
    return town


def extract_state(town: str) -> str:
    """Extract state code from a town field like '22 Collins St, Cranford, NJ'."""
    parts = [p.strip() for p in town.split(",") if p.strip()]
    if len(parts) >= 2 and len(parts[-1]) <= 3:
        return parts[-1].upper()
    return ""


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
        query += " AND LOWER(town) LIKE ?"
        params.append(f"%{town.lower()}%")
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
    if scare in ("family", "spooky", "terrifying"):
        query += " AND scare_level = ?"
        params.append(scare)
    if tag in ("animatronics", "inflatables", "handmade", "walkthrough", "projector", "lights", "music", "street-wide", "multi-house", "ticketed"):
        query += " AND (',' || COALESCE(tags,'') || ',') LIKE ?"
        params.append(f"%,{tag},%")
    query += f" ORDER BY {order} LIMIT 100"
    with get_conn(DB_PATH) as conn:
        entries = [row_to_dict(r) for r in conn.execute(query, params).fetchall()]
    voted = {k[6:] for k in request.cookies if k.startswith("voted_")}
    return templates.TemplateResponse(request, "index.html",
        {"request": request, "entries": entries, "sort": sort,
         "town": town, "towns": towns(cat, state), "states": states(cat),
         "state": state, "region": region, "voted": voted,
         "cat": cat, "cat_labels": CAT_LABELS, "cat_emoji": CAT_EMOJI,
         "scare": scare, "tag": tag},
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
    media: UploadFile = File(...),
):
    error: str | None = None
    title, town, display_name = title.strip()[:120], town.strip()[:80], display_name.strip()[:40]
    category = category if category in CATEGORIES else "halloween"
    scare_level = scare_level if scare_level in ("family", "spooky", "terrifying") else None
    # tags come as repeated form fields from checkboxes
    form = await request.form()
    tags = ",".join(sorted({t for t in form.getlist("tags")
                            if t in ("animatronics", "inflatables", "handmade", "walkthrough",
                                     "projector", "lights", "music", "street-wide",
                                     "multi-house", "ticketed")})) or None

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
    if not error and (not media or not media.filename):
        error = "Please attach a photo or video."

    entry_id = None
    if not error:
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
                    scare_level, tags)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?, 0, 0, 0, 0, ?, ?, ?, ?)""",
                (title, town, display_name or None, media_rel, thumb_rel,
                 media_type, lat_f, lng_f, category, now, scare_level, tags),
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
    return templates.TemplateResponse(request, "detail.html",
        {"request": request, "entry": entry, "voted": voted, "reported": reported,
         "tips": tips},
    )


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
    return templates.TemplateResponse(request, "stats.html",
        {"request": request, "total": total, "today": today, "week": week,
         "by_day": by_day, "top_pages": top_pages,
         "top_referrers": top_referrers, "by_device": by_device})


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
    scare = scare if scare in ("family", "spooky", "terrifying") else None
    tags = ",".join(sorted({t for t in form.getlist("tags")
                            if t in ("animatronics", "inflatables", "handmade", "walkthrough",
                                     "projector", "lights", "music", "street-wide",
                                     "multi-house", "ticketed")})) or None
    with get_conn(DB_PATH) as conn:
        conn.execute("UPDATE entries SET scare_level = ?, tags = ? WHERE id = ?",
                     (scare, tags, entry_id))
        conn.commit()
    return RedirectResponse("/admin", status_code=303)
