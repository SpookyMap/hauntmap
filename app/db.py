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
#   5653 NJ Park Ridge · 5654 NJ Fair Lawn · 5655 NJ Cherry Hill (Oct 24 Top 10 NJ batch)
#   5766 NJ Point Pleasant (Oct 25: Dan's showcase — the site's #1 pin
#   by interactions; also hand-picked below so it tops the homepage feed)
#   5572 NY Brooklyn (Oct 26: Dan's Top 10 NY pick — the Bay Ridge
#   holiday house, 635 79th St, from the @dj.darth.vader video; that
#   video was last-season footage of this already-posted display, so
#   the ⭐ lands on this existing pin and its embed stays untouched.
#   Featured only — this change does not touch the hand-picked list.)
#   5940 FL Orlando (Oct 26: Dan's send — @explore_orlando's TikTok
#   live room, a Featured Live pin mirroring Ghost Manor 171, the
#   site's original live-category pin; also hand-picked below.)
FEATURED_ENTRY_IDS = (5541, 5542, 5551, 5584, 5587, 5175, 4370, 5653, 5654, 5655, 5766, 5572, 5940)

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
# Oct 25 addition: 5766 (Point Pleasant NJ) — Dan's explicit showcase
# pick ("give the top pin some love"): the site's #1 pin by
# interactions. As the newest hand-picked pin it leads the homepage
# feed as the first card for every visitor.
# Oct 26 addition: 5940 (Orlando FL) — @explore_orlando's TikTok live
# room, sent by Dan personally ("add this to the live button and
# feature it"), so it joins this Dan-sent set as the newest entry.
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
    5610, 5611, 5612, 5613, 5614, 5615, 5616, 5617, 5618, 5766, 5940,
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
    viewed_at TEXT NOT NULL,              -- UTC ISO timestamp
    referrer TEXT,                        -- Referer header (admin traffic stats)
    device TEXT,                          -- coarse UA bucket: iOS/Android/Windows/Mac/Linux/Other
    sid TEXT,                             -- anonymous hm_sid session cookie id
    country TEXT,                         -- Cloudflare cf-ipcountry (Oct 26 geo stats); NULL on older rows
    region TEXT,                          -- cf-ipregion: US state code when resolvable, else CF's region name
    city TEXT                             -- cf-ipcity (needs CF's visitor-location transform); NULL when absent
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
    sid TEXT,                              -- 'engaged' rows only: visitor's hm_sid cookie (same id page_views stores)
    pvid TEXT,                             -- 'engaged' rows only: random per-page-load id minted by the beacon, so the deltas of ONE page view can be SUM-med into that view's dwell (per-page time-on-page stats, Oct 25); NULL on rows from before it existed
    source TEXT                            -- 'rail_click' rows only (Rail Boost, Oct 25): which rail the click came from (footage | town | near | near-here | like-this | explore); NULL on older rows and all other events
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
-- ------------------------------------------------ HauntMap Social (Phase 1)
-- Member accounts + profiles (plan: hauntmap-social-plan-2026-10-24.md).
-- Sessions are DATABASE-backed (the admin's in-memory set wipes on every
-- deploy; member sessions must not). Only the token HASH is stored.
CREATE TABLE IF NOT EXISTS users (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    email TEXT NOT NULL UNIQUE,           -- stored lowercase
    password_hash TEXT NOT NULL,          -- pbkdf2_hmac hex
    password_salt TEXT NOT NULL,          -- per-user salt hex
    handle TEXT NOT NULL UNIQUE,          -- lowercase, 3-20 chars [a-z0-9_]
    dob TEXT,                             -- ISO date, age gate at signup
    is_admin INTEGER NOT NULL DEFAULT 0,
    is_official INTEGER NOT NULL DEFAULT 0, -- 1 = official host (Frank)
    status TEXT NOT NULL DEFAULT 'active', -- active | suspended
    created_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_users_handle ON users(handle);
CREATE TABLE IF NOT EXISTS profiles (
    user_id INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    display_name TEXT,
    bio TEXT,
    town TEXT,                            -- hometown
    current_city TEXT,                    -- where they live now (edit-page only)
    avatar_choice TEXT,                   -- preset key, NULL = initial tile
    avatar_path TEXT,                     -- uploaded profile picture (rel path under uploads/); beats avatar_choice
    banner_choice TEXT,                   -- preset key, NULL = default banner
    theme TEXT,                           -- HauntSocial preset theme key
    music_embed_url TEXT,                 -- member-supplied Spotify/SC/YT URL
    website_url TEXT,
    -- "Get to know me" bundle (Dan, Oct 25): all optional, edit-page
    -- only, rendered on the profile only when set. Picks store keys
    -- validated against the GTK_* dicts in app/main.py.
    fav_joke TEXT,                        -- favorite Halloween joke (140)
    costume_pick TEXT,                    -- yes | no | undecided
    costume_as TEXT,                      -- dressing up as… (80)
    best_memory TEXT,                     -- best Halloween memory (500)
    scare_tolerance TEXT,                 -- a SCARE_LEVELS key
    haunter_kind TEXT,                    -- decorator | scare_actor | …
    candy_fav TEXT,                       -- favorite candy (60)
    candy_trade TEXT,                     -- candy they'd trade away (60)
    first_horror TEXT,                    -- first horror movie seen (120)
    monster_ego TEXT,                      -- vampire | ghost | werewolf | …
    haunt_name TEXT,                      -- my haunt this year: name (80)
    haunt_theme TEXT,                     -- my haunt this year: theme (80)
    season_start TEXT,                    -- sep1 | oct1 | yearround
    fav_song TEXT,                        -- favorite Halloween song (120)
    updated_at TEXT
);
CREATE TABLE IF NOT EXISTS sessions (
    token_hash TEXT PRIMARY KEY,          -- sha256 of the cookie token
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    created_at TEXT NOT NULL,
    expires_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_sessions_user ON sessions(user_id);
CREATE TABLE IF NOT EXISTS follows (
    follower_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    followee_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    created_at TEXT NOT NULL,
    UNIQUE (follower_id, followee_id)
);
CREATE TABLE IF NOT EXISTS wall_comments (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    profile_user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    author_user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    text TEXT NOT NULL,
    sticker TEXT,                         -- HauntSocial treat sticker (emoji)
    hidden INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_wall_profile ON wall_comments(profile_user_id, created_at);
-- HauntSocial Phase A: "My Top 8" — THINGS, never people (research
-- guardrail): each slot is a HauntMap pin or a favorite horror film.
CREATE TABLE IF NOT EXISTS profile_top8 (
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    slot INTEGER NOT NULL,                -- 1..8, display order
    kind TEXT NOT NULL,                   -- 'haunt' | 'film'
    entry_id INTEGER REFERENCES entries(id) ON DELETE CASCADE,
    film_title TEXT,
    PRIMARY KEY (user_id, slot)
);
-- HauntSocial photo uploads (Dan, Oct 25): a member's own photos on
-- their profile page. Files live under uploads/photos/ + uploads/thumbs/;
-- the uploaded profile picture itself is profiles.avatar_path.
CREATE TABLE IF NOT EXISTS profile_photos (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    path TEXT NOT NULL,                   -- rel path under uploads/ (photos/…)
    thumb_path TEXT,                      -- rel thumb path under uploads/ (thumbs/…)
    created_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_profile_photos_user ON profile_photos(user_id, id);
-- HauntSocial passport stamps (#11, Dan, Oct 25): the per-user mirror
-- of the device-local hm_seen set (templates/base.html). Rows are
-- written ONLY by the authenticated union merge in
-- POST /api/passport/sync; anonymous passport progress never leaves
-- the visitor's device and never reaches this table. One row per
-- (member, pin): re-syncing is a no-op, and a second device ADDS to
-- the same collection instead of overwriting the first one's.
CREATE TABLE IF NOT EXISTS passport_stamps (
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    entry_id INTEGER NOT NULL REFERENCES entries(id) ON DELETE CASCADE,
    stamped_at TEXT NOT NULL,
    PRIMARY KEY (user_id, entry_id)
);
CREATE INDEX IF NOT EXISTS idx_passport_stamps_user ON passport_stamps(user_id, stamped_at);
-- GHOST MAZE member leaderboard (Dan, Oct 25): one row per member —
-- their best GHOST MAZE score, kept by the authenticated submit in
-- POST /api/games/ghost-maze/score (best-only upsert, server-side
-- plausibility cap). Anonymous players keep a device-local best and
-- never reach this table.
CREATE TABLE IF NOT EXISTS game_scores (
    user_id INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    best_score INTEGER NOT NULL DEFAULT 0,
    achieved_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS reports (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    reporter_user_id INTEGER REFERENCES users(id),
    target_type TEXT NOT NULL,            -- profile | comment | pin
    target_id INTEGER NOT NULL,
    reason TEXT,
    status TEXT NOT NULL DEFAULT 'open',  -- open | reviewed | actioned
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS blocks (
    blocker_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    blocked_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    created_at TEXT NOT NULL,
    UNIQUE (blocker_id, blocked_id)
);
CREATE TABLE IF NOT EXISTS password_reset_requests (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    email TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'queued', -- queued | sent | done
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS social_meta (
    key TEXT PRIMARY KEY,
    value TEXT
);
"""


def get_conn(db_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(str(db_path), timeout=5.0)
    conn.row_factory = sqlite3.Row
    # WAL + busy timeout (blip hardening, Oct 25): in WAL mode readers
    # never block the single writer and the writer never blocks readers;
    # a write that still finds the database contended waits up to 5s for
    # the lock instead of failing with "database is locked" — the failure
    # mode behind the Oct 24 stall/restart cycle. WAL is persistent on
    # the database file once set, so the per-connection pragma is a
    # no-op reaffirm after the first connection.
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA busy_timeout=5000")
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
        for col, ddl in (("path", "TEXT"), ("seconds", "INTEGER"), ("sid", "TEXT"),
                         ("source", "TEXT"), ("pvid", "TEXT")):
            if col not in ecols:
                conn.execute(f"ALTER TABLE engagement_events ADD COLUMN {col} {ddl}")
        # Page-view analytics columns (blip hardening, Oct 25): referrer /
        # device / sid used to be added by per-request CREATE/ALTER
        # statements inside the tracking middleware — synchronous DDL on
        # the event loop for every page view, a root cause of the Oct 24
        # stalls. They are ensured HERE, at startup, instead; the request
        # path never runs DDL.
        pvcols = {r["name"] for r in conn.execute("PRAGMA table_info(page_views)").fetchall()}
        for col in ("referrer", "device", "sid"):
            if col not in pvcols:
                conn.execute(f"ALTER TABLE page_views ADD COLUMN {col} TEXT")
        # Visitor geography (Dan, Oct 26): country / region / city from
        # Cloudflare's headers, captured per page view for the /admin
        # "Visitors by geography" panel. Same startup-ensure pattern —
        # the request path never runs DDL. Older rows stay NULL (no
        # backfill is possible); the index is created HERE, after the
        # columns exist, never in SCHEMA (an index on a not-yet-added
        # column would fail init on existing DBs).
        for col in ("country", "region", "city"):
            if col not in pvcols:
                conn.execute(f"ALTER TABLE page_views ADD COLUMN {col} TEXT")
        conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_page_views_country "
            "ON page_views(country)")
        # HauntMap Social (Phase 1): a pin's owner once a haunter claims
        # it. NULL until claimed; profile "My haunts" reads this column.
        if "owner_user_id" not in cols:
            conn.execute("ALTER TABLE entries ADD COLUMN owner_user_id INTEGER")
        # HauntSocial Phase A: official-host flag, profile themes,
        # wall treat stickers — for DBs created before they existed.
        ucols = {r["name"] for r in conn.execute("PRAGMA table_info(users)").fetchall()}
        if ucols and "is_official" not in ucols:
            conn.execute(
                "ALTER TABLE users ADD COLUMN is_official INTEGER NOT NULL DEFAULT 0")
        pcols = {r["name"] for r in conn.execute("PRAGMA table_info(profiles)").fetchall()}
        if pcols and "theme" not in pcols:
            conn.execute("ALTER TABLE profiles ADD COLUMN theme TEXT")
        if pcols and "avatar_path" not in pcols:
            conn.execute("ALTER TABLE profiles ADD COLUMN avatar_path TEXT")
        if pcols and "current_city" not in pcols:
            conn.execute("ALTER TABLE profiles ADD COLUMN current_city TEXT")
        # "Get to know me" bundle columns (Dan, Oct 25) — same pattern.
        for gtk_col in ("fav_joke", "costume_pick", "costume_as",
                        "best_memory", "scare_tolerance", "haunter_kind",
                        "candy_fav", "candy_trade", "first_horror",
                        "monster_ego", "haunt_name", "haunt_theme",
                        "season_start", "fav_song"):
            if pcols and gtk_col not in pcols:
                conn.execute(
                    f"ALTER TABLE profiles ADD COLUMN {gtk_col} TEXT")
        wcols = {r["name"] for r in conn.execute("PRAGMA table_info(wall_comments)").fetchall()}
        if wcols and "sticker" not in wcols:
            conn.execute("ALTER TABLE wall_comments ADD COLUMN sticker TEXT")
        conn.commit()
