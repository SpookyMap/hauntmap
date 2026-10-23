"""SQLite layer for HauntMap. Synchronous sqlite3 — fine for MVP traffic.

Schema note: votes are a plain counter; the one-vote-per-browser rule is
enforced with cookies in main.py (a soft limit, documented there).
"""
import sqlite3
from pathlib import Path

SCHEMA = """
CREATE TABLE IF NOT EXISTS comments (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    entry_id INTEGER NOT NULL REFERENCES entries(id) ON DELETE CASCADE,
    display_name TEXT,
    text TEXT NOT NULL,
    hidden INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS subscribers (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    email TEXT NOT NULL UNIQUE,
    location TEXT,                        -- town, county, or 'everywhere'
    created_at TEXT NOT NULL
);
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
    tags TEXT,                            -- comma-separated: animatronics,inflatables,handmade,walkthrough,projector,lights,music,street-wide,multi-house
    ev_type TEXT,                         -- events facet: event type (see EVENT_TYPES in main.py)
    ev_genre TEXT,                        -- events facet: music genre (see EVENT_GENRES in main.py)
    ev_venue TEXT                         -- events facet: venue style (see EVENT_VENUES in main.py)
);
CREATE INDEX IF NOT EXISTS idx_entries_town ON entries(town);
CREATE INDEX IF NOT EXISTS idx_entries_votes ON entries(votes DESC);
CREATE TABLE IF NOT EXISTS page_views (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    path TEXT NOT NULL,                   -- URL path visited, e.g. "/" or "/d/5"
    viewed_at TEXT NOT NULL               -- UTC ISO timestamp
);
CREATE INDEX IF NOT EXISTS idx_page_views_date ON page_views(viewed_at);
CREATE TABLE IF NOT EXISTS sponsors (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    business_name TEXT NOT NULL,
    logo_path TEXT,                  -- path relative to uploads dir, e.g. "sponsors/abc123.jpg"
    website_url TEXT NOT NULL,
    tier TEXT NOT NULL DEFAULT 'featured', -- 'featured' | 'premium' | 'title'
    banner_text TEXT,
    is_active INTEGER NOT NULL DEFAULT 1,
    clicks INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_sponsors_active ON sponsors(is_active);
CREATE TABLE IF NOT EXISTS sms_subscribers (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    phone TEXT NOT NULL UNIQUE,           -- E.164, e.g. +19735551234
    zip TEXT,                             -- 5-digit ZIP (radius matching)
    town TEXT,                            -- subscriber's town (town-only matching)
    state TEXT,                           -- 2-letter state for the town
    radius_miles INTEGER NOT NULL DEFAULT 15,  -- 0 = my town only
    interests TEXT NOT NULL DEFAULT 'both',    -- 'haunts' | 'events' | 'both'
    consent_at TEXT NOT NULL,             -- UTC ISO timestamp of web opt-in
    status TEXT NOT NULL DEFAULT 'captured',   -- captured | confirmed | opted_out
    confirm_code TEXT,                    -- 6-digit code while status=captured
    confirm_expires TEXT,                 -- UTC ISO expiry for the code
    source TEXT,                          -- page the signup came from
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS engagement_events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    created_at TEXT NOT NULL,             -- UTC ISO timestamp
    event TEXT NOT NULL,                   -- video_play | tour_add | next_bar_click | rail_click | vote | unvote | scare | tip
    entry_id INTEGER,                      -- pin the interaction is attributed to, NULL when not pin-bound
    town TEXT                              -- pin's town label, derived server-side from entry_id
);
CREATE INDEX IF NOT EXISTS idx_engagement_created_event ON engagement_events(created_at, event);
CREATE INDEX IF NOT EXISTS idx_engagement_entry ON engagement_events(entry_id);
CREATE INDEX IF NOT EXISTS idx_sms_subscribers_status ON sms_subscribers(status);
CREATE TABLE IF NOT EXISTS sms_sends (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    subscriber_id INTEGER NOT NULL REFERENCES sms_subscribers(id),
    kind TEXT NOT NULL,                   -- 'confirm' | 'digest'
    body TEXT NOT NULL,
    pin_ids TEXT,                         -- comma-separated entry ids in a digest
    twilio_sid TEXT,
    status TEXT NOT NULL DEFAULT 'queued', -- queued | sent | failed | dry_run
    created_at TEXT NOT NULL
);
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
        if "address" not in cols:
            # Verified street address (address-audit cleanup, Oct 2026).
            # NULL until the pin's address has been verified; stored
            # separately so title/town stay display text.
            conn.execute("ALTER TABLE entries ADD COLUMN address TEXT")
        if "description" not in cols:
            # Free-text description sent by posting crews via /upload
            # (Oct 2026). NULL when not provided.
            conn.execute("ALTER TABLE entries ADD COLUMN description TEXT")
        # Events facets (Dan, Oct 22): event type / music genre / venue
        # style powering the /events filter dropdowns. NULL = untagged;
        # only set when a listing plainly determines the value.
        for col in ("ev_type", "ev_genre", "ev_venue"):
            if col not in cols:
                conn.execute(f"ALTER TABLE entries ADD COLUMN {col} TEXT")
        conn.commit()
