# HauntMap 🎃

Mobile-first web app where people upload photos/videos of the best Halloween
decorations by neighborhood, vote on favorites, and browse town leaderboards.

**Stack:** Python FastAPI + Jinja2 + SQLite + local disk uploads. Leaflet.js
(CDN) for maps. No accounts, no payments, no email in v1 — deliberately lean
so it can ship before Halloween.

## Quick start (local)

```bash
cd hauntmap
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt

# Optional: seed 3 clearly-labeled SAMPLE entries so the site isn't empty
python -m app.seed

# Run it (ADMIN_PASSWORD defaults to "haunt-admin" — change it below)
ADMIN_PASSWORD=haunt-admin uvicorn app.main:app --reload
```

Open http://127.0.0.1:8000

Pages: `/` feed · `/upload` · `/d/{id}` detail · `/leaderboard` · `/admin`

## Configuration

Environment variables (see `.env.example`):

| Variable         | Default      | What it does                                    |
|------------------|--------------|-------------------------------------------------|
| `ADMIN_PASSWORD` | `haunt-admin`| Password for `/admin` (flagged-entry moderation) |
| `SITE_NAME`      | `HauntMap`   | Site name in header, titles, footer             |
| `DATA_DIR`       | `./data`     | Where `hauntmap.db` (SQLite) lives              |
| `UPLOAD_DIR`     | `./uploads`  | Where uploaded photos/videos + thumbnails live  |

**Change the admin password:** set `ADMIN_PASSWORD` to something strong in
your shell or host's env settings before going live. There is no
"change password" UI — the env var *is* the password.

**Change the site name:** set `SITE_NAME` and restart.

**Remove the sample entries:** log in at `/admin` and delete the three
entries badged "Sample" (or hide them to keep them out of the feed without
deleting the files).

## Deploy

### Option A — Render (free tier)

1. Push this folder to a GitHub repo.
2. Render dashboard → **New → Web Service** → connect the repo.
3. Runtime: **Docker**. Render builds the `Dockerfile` automatically.
4. Add environment variables: `ADMIN_PASSWORD` (strong value), `SITE_NAME`.
5. ⚠️ **Free-tier caveat:** Render's free disks are ephemeral — uploaded
   photos/videos and the SQLite DB are wiped on every redeploy/restart.
   For a real launch, attach a **Persistent Disk** (paid) mounted at
   `/srv/data` and `/srv/uploads`, or accept that content resets.

### Option B — Railway (free tier)

1. Push to GitHub → Railway **New Project → Deploy from repo**.
2. Railway detects the `Dockerfile` and builds it.
3. Add variables: `ADMIN_PASSWORD`, `SITE_NAME` under **Variables**.
4. ⚠️ Same ephemeral-disk caveat as Render: add a **Volume** mounted at
   `/srv/data` and `/srv/uploads` to keep uploads + DB across deploys.

### Health check

`GET /` returning 200 is the health check. The app creates `data/` and
`uploads/` on startup if missing.

## Notes & limits (v1)

- **Votes:** one vote per browser per entry via cookie. This is a soft
  limit — clearing cookies allows re-voting. Fine for an MVP, not for
  anything with prizes on the line.
- **Uploads:** photos JPG/PNG/WebP ≤ 10 MB (Pillow thumbnail generated);
  video MP4 ≤ 50 MB (magic-byte checked for `ftyp`). Filenames are replaced
  with UUIDs; only the extension is kept.
- **Moderation:** visitors can report entries (`/d/{id}` → Report). Flagged
  entries appear in `/admin` with Hide / Unhide / Delete.
- **Maps:** Leaflet + OpenStreetMap tiles via CDN. Uploads get an optional
  tap-to-drop pin; detail pages show the pin when set. If the CDN is
  unreachable, the map areas stay blank but everything else works.
- **Categories:** entries carry a `category` (`'halloween'` → 🎃 Haunt Map tab,
  `'christmas'` → 🎄 Jolly Map tab, `'food'` reserved for the post-holiday food
  section) plus `food_subcategory` (e.g. `coffee`, `pizza`) and `tiktok_url`.
  Feed, leaderboard, and upload all filter/select by category — no schema
  rebuild needed to add sections. Older DBs are migrated automatically on startup.
- **Scale:** single uvicorn worker + SQLite. Good for hundreds of daily
  visitors; revisit if it takes off.

## Project layout

```
hauntmap/
├── app/
│   ├── main.py      # FastAPI app: routes, uploads, voting, admin
│   ├── db.py        # SQLite schema + helpers
│   └── seed.py      # generates 3 SAMPLE entries
├── templates/       # Jinja2: base, index, upload, detail, leaderboard, admin
├── static/css/      # hand-rolled mobile-first Halloween theme
├── data/            # SQLite DB (created on first run)
├── uploads/         # user media + thumbs/ (created on first run)
├── Dockerfile
├── requirements.txt
└── README.md
```
