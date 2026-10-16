"""SQLite layer for HauntMap. Synchronous sqlite3 — fine for MVP traffic.

Schema note: votes are a plain counter; the one-vote-per-browser rule is
enforced with cookies in main.py (a soft limit, documented there).
"""
import sqlite3
from pathlib import Path

SCHEMA = """
CREATE TABLE IF NOT EXISTS entries (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    title TEXT NOT NULL,
    town TEXT NOT NULL,
    display_name TEXT,
    media_path TEXT NOT NULL,   -- path relative to the uploads dir, e.g. "abc123.jpg"
    thumb_path TEXT,            -- relative path of photo thumbnail, NULL for video
    media_type TEXT NOT NULL,   -- 'photo' | 'video'
    lat REAL,                   -- optional map pin
    lng REAL,
    votes INTEGER NOT NULL DEFAULT 0,
    flagged INTEGER NOT NULL DEFAULT 0,   -- 1 when a visitor reported it
    hidden INTEGER NOT NULL DEFAULT 0,    -- 1 hides it from public pages (admin action)
    is_sample INTEGER NOT NULL DEFAULT 0, -- 1 for seeded demo entries
    -- Future "food & drink" section (post-Halloween). V1 UI stays Halloween-only;
    -- these columns let the food section ship without a schema rebuild.
    category TEXT NOT NULL DEFAULT 'halloween', -- 'halloween' | 'food'
    food_subcategory TEXT,                -- e.g. 'coffee', 'pizza', 'croissant'
    tiktok_url TEXT,                      -- optional TikTok video link
    created_at TEXT NOT NULL,             -- UTC ISO timestamp
    scare_level TEXT,                     -- 'family' | 'spooky' | 'terrifying'
    tags TEXT                             -- comma-separated: animatronics,inflatables,handmade,walkthrough,projector,lights,music
);
CREATE INDEX IF NOT EXISTS idx_entries_town ON entries(town);
CREATE INDEX IF NOT EXISTS idx_entries_votes ON entries(votes DESC);
"""


def get_conn(db_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(str(db_path))
    conn.row_factory = sqlite3.Row
    return conn


def init_db(db_path: Path) -> None:
    db_path.parent.mkdir(parents=True, exist_ok=True)
    with get_conn(db_path) as conn:
        conn.executescript(SCHEMA)
        # Migrate DBs created before the food-section columns existed.
        cols = {r["name"] for r in conn.execute("PRAGMA table_info(entries)").fetchall()}
        if "category" not in cols:
            conn.execute(
                "ALTER TABLE entries ADD COLUMN category TEXT NOT NULL DEFAULT 'halloween'"
            )
        if "food_subcategory" not in cols:
            conn.execute("ALTER TABLE entries ADD COLUMN food_subcategory TEXT")
        if "tiktok_url" not in cols:
            conn.execute("ALTER TABLE entries ADD COLUMN tiktok_url TEXT")
        if "scare_level" not in cols:
            conn.execute("ALTER TABLE entries ADD COLUMN scare_level TEXT")
        if "tags" not in cols:
            conn.execute("ALTER TABLE entries ADD COLUMN tags TEXT")
        conn.commit()
