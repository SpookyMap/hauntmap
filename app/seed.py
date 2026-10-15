"""Seed HauntMap with 3 clearly-labeled SAMPLE entries so the site isn't
empty on launch. Generates simple Halloween-styled placeholder images with
Pillow and inserts rows flagged is_sample=1 (shown with a "Sample" badge in
the UI, deletable from /admin).

Run:  python -m app.seed   (from the project root)
Re-running is safe: it skips seeding if any sample entries already exist.
"""
import sqlite3
import uuid
from datetime import datetime, timezone
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

from .db import get_conn, init_db

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = Path(__import__("os").environ.get("DATA_DIR", BASE_DIR / "data"))
UPLOAD_DIR = Path(__import__("os").environ.get("UPLOAD_DIR", BASE_DIR / "uploads"))

SAMPLES = [
    {
        "title": "The Skeleton Orchestra House",
        "town": "Salem",
        "display_name": "Sample",
        "blurb": "12-ft skeletons playing instruments",
        "accent": (255, 123, 28),
    },
    {
        "title": "Pumpkin Lane Takeover",
        "town": "Sleepy Hollow",
        "display_name": "Sample",
        "blurb": "40 carved jack-o'-lanterns down the block",
        "accent": (255, 170, 40),
    },
    {
        "title": "Graveyard on Elm Street",
        "town": "Salem",
        "display_name": "Sample",
        "blurb": "Fog machines + tombstones + ghosts",
        "accent": (178, 102, 255),
    },
]

W, H = 900, 600


def make_image(title: str, blurb: str, accent: tuple) -> Image.Image:
    img = Image.new("RGB", (W, H), (16, 10, 26))
    d = ImageDraw.Draw(img)
    # vertical gradient: deep purple -> near black
    for y in range(H):
        t = y / H
        d.line([(0, y), (W, y)], fill=(int(30 - 14 * t), int(16 - 8 * t), int(48 - 26 * t)))
    # big moon
    d.ellipse([W - 300, 40, W - 60, 280], fill=accent)
    d.ellipse([W - 280, 60, W - 80, 260], fill=(24, 14, 38))  # crescent cutout
    # bats: simple arcs
    for bx, by, s in [(120, 90, 26), (210, 140, 18), (700, 330, 22), (90, 400, 16)]:
        d.arc([bx - s, by - s // 2, bx + s, by + s // 2], 200, 340, fill=(10, 6, 18), width=5)
    # ground silhouette
    d.rectangle([0, H - 120, W, H], fill=(8, 5, 14))
    # text
    font_big = ImageFont.load_default(size=44)
    font_small = ImageFont.load_default(size=26)
    d.text((40, H - 260), "SAMPLE", font=font_big, fill=(255, 255, 255))
    d.text((40, H - 200), title, font=font_small, fill=accent)
    d.text((40, H - 160), blurb, font=font_small, fill=(200, 180, 220))
    return img


def main() -> None:
    import os

    db_path = Path(os.environ.get("DATA_DIR", str(DATA_DIR))) / "hauntmap.db"
    upload_dir = Path(os.environ.get("UPLOAD_DIR", str(UPLOAD_DIR)))
    init_db(db_path)
    upload_dir.mkdir(parents=True, exist_ok=True)

    with get_conn(db_path) as conn:
        existing = conn.execute(
            "SELECT COUNT(*) AS c FROM entries WHERE is_sample = 1"
        ).fetchone()["c"]
        if existing:
            print(f"Seed skipped: {existing} sample entries already present.")
            return
        now = datetime.now(timezone.utc).isoformat()
        for s in SAMPLES:
            fname = f"sample-{uuid.uuid4().hex[:8]}.jpg"
            make_image(s["title"], s["blurb"], s["accent"]).save(
                upload_dir / fname, "JPEG", quality=82
            )
            conn.execute(
                """INSERT INTO entries
                   (title, town, display_name, media_path, thumb_path, media_type,
                    votes, flagged, hidden, is_sample, created_at)
                   VALUES (?, ?, ?, ?, ?, 'photo', ?, 0, 0, 1, ?)""",
                (s["title"], s["town"], s["display_name"], fname, fname, 0, now),
            )
        conn.commit()
    print(f"Seeded {len(SAMPLES)} sample entries.")


if __name__ == "__main__":
    main()
