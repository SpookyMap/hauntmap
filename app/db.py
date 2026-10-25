"""SQLite layer for HauntMap. Synchronous sqlite3 — fine for MVP traffic.

Schema note: votes are a plain counter; the one-vote-per-browser rule is
enforced with cookies in main.py (a soft limit, documented there).
"""
import sqlite3
from pathlib import Path

# Editor's-pick pins (Dan, Oct 23): hand-picked "feature as Top 10"
# placements, guaranteed a slot in their state's Top 10 list (and the
# sitewide Top Haunts board) with an honest ⭐ Featured marker. The
# list is code-owned and enforced by init_db on every boot, so the
# flagged set is exactly these pins and survives deploys/restarts.
# Ranking data (views/votes) is never altered. No DMV pick: Dan ruled
# his Silver Spring (DMV) candidate stays held (2024 video).
#   5541 NC Wake Forest · 5542 SC Mauldin · 5551 CA Mission Viejo
#   5584 CA Santa Fe Springs · 5587 OR Happy Valley
#   5175 IL Oak Lawn · 4370 CO Denver
FEATURED_ENTRY_IDS = (5541, 5542, 5551, 5584, 5587, 5175, 4370, 5653)

# Hand-picked pins (Dan, Oct 23): pins Dan personally sent in chat or
# curated for posting. These lead every feed view — hand-picked first
# (newest hand-picked first), then all other pins newest-first — per
# Dan's feed-order rule. The list is code-owned and enforced by
# init_db on every boot, so the flagged set is exactly these pins and
# survives deploys/restarts (same mechanism as the Top 10 editor's
# picks). To extend: append the new pin ids here and deploy — the
# posting flows record Dan's sends, this list is the durable marker.
# Provenance of the initial set (all Oct 23, 2026):
#   * posting-log entries carrying a dan_* source marker
#     (dan_feed_add / dan_top10_feed / dan_tour_feed / dan_creator_feed
#     / dan_toks): 5065, 5105, 5540, 5541, 5542, 5548, 5552-5563,
#     5595-5618
#   * pins posted from links Dan sent in chat on Oct 23 whose log
#     entries carry no source marker (Naperville / Whittier / Mission
#     Viejo / UES tour runs and the 35-link batch): 5543-5547, 5549,
#     5550, 5551, 5564-5570, 5571-5593
#   * already-live pins whose displays Dan sent links for on Oct 23
#     (incl. his Top 10 Illinois / Colorado picks and tour stops that
#     were already posted): 805, 930, 936, 4370, 4372-4377, 4384,
#     4395, 4465, 4546, 4548, 4550, 4557-4562, 4594, 4595, 4681,
#     4925, 5175, 5308
# Dan's sends from Oct 15-22 predate source marking in the posting log
# and are NOT in this set — the log cannot identify them reliably.
HANDPICKED_ENTRY_IDS = (
    805, 930, 936, 4370, 4372, 4373, 4374, 4375, 4376, 4377, 4384,
    4395, 4465, 4546, 4548, 4550, 4557, 4558, 4559, 4560, 4561, 4562,
    4594, 4595, 4681, 4925, 5065, 5105, 5175, 5308, 5540, 5541, 5542,
    5543, 5544, 5545, 5546, 5547, 5548, 5549, 5550, 5551, 5552, 5553,
    5554, 5555, 5556, 5557, 5558, 5559, 5560, 5561, 5562, 5563, 5564,
    5565, 5566, 5567, 5568, 5569, 5570, 5571, 5572, 5573, 5574, 5575,
    5576, 5577, 5578, 5579, 5580, 5581, 5582, 5583, 5584, 5585, 5586,
    5587, 5588, 5589, 5590, 5591, 5592, 5593, 5595, 5596, 5597, 5598,
    5599, 5600, 5601, 5602, 5603, 5604, 5605, 5606, 5607, 5608, 5609,
    5610, 5611, 5612, 5613, 5614, 5615, 5616, 5617, 5618,
)

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
    is_featured INTEGER NOT NULL DEFAULT 0, -- 1 for editor's-pick pins (Dan's hand-picked Top 10 placements)
    is_handpicked INTEGER NOT NULL DEFAULT 0, -- 1 for Dan's hand-picked pins (feed boost, see HANDPICKED_ENTRY_IDS)    -- Future "food & drink" section (post-Halloween). V1 UI stays Halloween-only;
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
CREATE TABLE IF NOT EXISTS shared_tours (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    slug TEXT NOT NULL UNIQUE,            -- URL-safe token, /t/{slug}
    title TEXT NOT NULL,                  -- e.g. "My Fright Night — Seekonk, MA"
    pin_ids TEXT NOT NULL,                -- JSON array of entry ids, array order = tour order
    created_at TEXT NOT NULL,             -- UTC ISO timestamp
    views INTEGER NOT NULL DEFAULT 0      -- GET /t/{slug} loads (verification UA excluded)
);
CREATE TABLE IF NOT EXISTS engagement_events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    created_at TEXT NOT NULL,             -- UTC ISO timestamp
    event TEXT NOT NULL,                   -- video_play | tour_add | next_bar_click | rail_click | vote | unvote | scare | tip | engaged
    entry_id INTEGER,                      -- pin the interaction is attributed to, NULL when not pin-bound
    town TEXT,                             -- pin's town label, derived server-side from entry_id
    path TEXT,                             -- 'engaged' rows only: page path the time was spent on
    seconds INTEGER,                       -- 'engaged' rows only: incremental engaged seconds (clamped server-side)
    sid TEXT                               -- 'engaged' rows only: visitor's hm_sid cookie (same id page_views stores)
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
        if "is_featured" not in cols:
            # Editor's-pick flag (Top 10 by State staging): Dan's
            # hand-picked pins are guaranteed a slot in their state's
            # Top 10 (and in the sitewide Top Haunts) with an honest
            # "Featured" marker. Ranking data (views/votes) is never
            # altered — the flag only affects list placement.
            conn.execute(
                "ALTER TABLE entries ADD COLUMN is_featured INTEGER NOT NULL DEFAULT 0"
            )
        # Enforce the code-owned editor's-pick set (FEATURED_ENTRY_IDS):
        # exactly those pins flagged, every other pin unflagged. Runs on
        # every init (idempotent) so the set survives deploys/restarts.
        _ph = ",".join("?" * len(FEATURED_ENTRY_IDS))
        conn.execute(
            f"UPDATE entries SET is_featured = 1 WHERE id IN ({_ph})",
            FEATURED_ENTRY_IDS,
        )
        conn.execute(
            "UPDATE entries SET is_featured = 0 "
            f"WHERE is_featured != 0 AND id NOT IN ({_ph})",
            FEATURED_ENTRY_IDS,
        )
        if "is_handpicked" not in cols:
            # Hand-picked feed boost (Dan, Oct 23): pins Dan personally
            # sent/curated lead every feed. Ranking data is never
            # altered — the flag only affects default list placement.
            conn.execute(
                "ALTER TABLE entries ADD COLUMN is_handpicked INTEGER NOT NULL DEFAULT 0"
            )
        # Enforce the code-owned hand-picked set (HANDPICKED_ENTRY_IDS):
        # exactly those pins flagged, every other pin unflagged. Runs
        # on every init (idempotent) so the set survives deploys.
        _hp = ",".join("?" * len(HANDPICKED_ENTRY_IDS))
        conn.execute(
            f"UPDATE entries SET is_handpicked = 1 WHERE id IN ({_hp})",
            HANDPICKED_ENTRY_IDS,
        )
        conn.execute(
            "UPDATE entries SET is_handpicked = 0 "
            f"WHERE is_handpicked != 0 AND id NOT IN ({_hp})",
            HANDPICKED_ENTRY_IDS,
        )
        # Events facets (Dan, Oct 22): event type / music genre / venue
        # style powering the /events filter dropdowns. NULL = untagged;
        # only set when a listing plainly determines the value.
        for col in ("ev_type", "ev_genre", "ev_venue"):
            if col not in cols:
                conn.execute(f"ALTER TABLE entries ADD COLUMN {col} TEXT")
        # Retention Wave 2, Item 6: engaged-time beacon columns on
        # engagement_events (path / seconds / sid) for DBs created before
        # the beacon existed. main.py also ensures these lazily on insert.
        ecols = {r["name"] for r in conn.execute("PRAGMA table_info(engagement_events)").fetchall()}
        for col, ddl in (("path", "TEXT"), ("seconds", "INTEGER"), ("sid", "TEXT")):
            if col not in ecols:
                conn.execute(f"ALTER TABLE engagement_events ADD COLUMN {col} {ddl}")
        conn.commit()
