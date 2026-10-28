"""SQLite layer for HauntMap. Synchronous sqlite3 — fine for MVP traffic.

Schema note: votes are a plain counter; the one-vote-per-browser rule is
enforced with cookies in main.py (a soft limit, documented there).
"""
import sqlite3
from datetime import datetime, timezone
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
#   6006 CA San Jose (Oct 27: Dan's Top 10 CA pick — the Gory
#   Operation Theatre House, 1360 Tenaya Dr, restored today as 6006
#   after the Oct 26 purge deleted its original pin 4566; one of the
#   site's highest-interaction pins. Featured only — this change does
#   not touch the hand-picked list.)
#   116 NY Croton-on-Hudson (Oct 27: Dan's "Top 10" pick — the Great
#   Jack O'Lantern Blaze at Van Cortlandt Manor, 525 S Riverside Ave;
#   the pin already existed as an events pin, so no duplicate was
#   posted and @suzebauer's TikTok of the Blaze was attached to it.
#   Featured only — the hand-picked list is untouched.)
#   6084 NJ Fair Lawn (Oct 27: Dan's "Top 10" pick — Halloween House,
#   17-05 Ellis Ave, @lilroamingexplorers Part 14, posted today as
#   pin 6084. Featured only — the hand-picked list is untouched.)
#   4932 IL Orland Park (Oct 27: Dan's "All top 10" burst pick —
#   Gloomy Oaks Manor, 12351 Derby Lane; the pin already existed
#   with no video, so no duplicate was posted and the creator's own
#   TikTok (@gloomyoaksmanor) was attached to it below. Featured
#   only — the hand-picked list is untouched.)
#   6085 FL Kissimmee (Oct 27: Dan's "All top 10" burst pick —
#   Mortem Manor, 5770 W Irlo Bronson Memorial Hwy, posted today as
#   pin 6085 via @hiddenshorestravel's TikTok. Featured only — the
#   hand-picked list is untouched.)
#   6086 CA Sacramento (Oct 27: Dan's "All top 10" burst pick —
#   Phantom Manor, 875 Rancho Roble Way; the interactive Halloween
#   Scavenger Haunt home haunt from @ulyssesbaltazar's TikTok,
#   posted today as pin 6086. Featured only — the hand-picked
#   list is untouched.)
#   30 NJ Ridgewood (Oct 27: Dan's "All top 10" burst pick —
#   Ridgewood Halloween House, 294 West End Ave; the pin already
#   existed with no video, so no duplicate was posted and
#   @growingwithju's TikTok was attached to it below. Featured
#   only — the hand-picked list is untouched.)
#   6098 IL Chicago (Oct 27: Dan's "All top 10" burst pick —
#   Grimm's Carnevil, 11045 S St Louis Ave; the free Mount
#   Greenwood walk-through home haunt from @yourhappilylove's
#   TikTok, posted today as pin 6098. Featured only — the
#   hand-picked list is untouched.)
#   6096 NY Monroe (Oct 27: Dan's "Longest haunted house in the
#   world — top ten and top 100" pick — Pure Terror Scream Park,
#   1008 NY-17M; the Guinness-certified longest horror attraction
#   (6,344 ft route, certified 2015), posted today as pin 6096 via
#   @savannahvinsonn's TikTok. Featured only — the hand-picked
#   list is untouched.)
#   1641 PA Bethel Park (Oct 27: Dan's "All top 10" burst pick —
#   Hundred Acres Manor, 2133 100 Acres Drive; the pin already
#   existed in haunted_houses with no video, so no duplicate was
#   posted and @dreadalertmedia's TikTok review of the manor's
#   five attractions was attached to it below. Featured only —
#   the hand-picked list is untouched.)
#   6092 CA San Diego (Oct 27: Dan's "All top 10" burst pick —
#   Whaley House Museum, 2476 San Diego Ave; the year-round
#   haunted house museum in Old Town San Diego, billed as
#   America's most haunted house, posted today as pin 6092 in
#   haunted_houses via @fablittledish's TikTok. Featured only —
#   the hand-picked list is untouched.)
#   6100 NV Elko (Oct 27: Dan's "All top 10" burst pick —
#   Haunted Commercial Hotel, 345 4th St; the two-haunted-house
#   attraction (Check In + Night Shift) inside Elko's historic
#   Commercial Hotel from @commercial.fun's TikTok, posted
#   today as pin 6100. Featured only — the hand-picked list
#   is untouched.)
#   6099 CA Temecula (Oct 27: Dan's "All top 10" burst pick —
#   Anton Haunt, 42330 Wyandotte St; the long-running home haunt
#   (18th year in 2026) from @susanscottphotography's TikTok,
#   posted today as pin 6099. Featured only — the hand-picked
#   list is untouched.)
#   haunted house (since 2003, 2026 season Oct 3-31) from
#   @cazsavaa's TikTok, posted today as pin 6101. Featured only —
#   the hand-picked list is untouched.)
#   Dread Alert Media review pins (Oct 27: Dan named the haunt-review
#   account @dreadalertmedia a featured review partner — "all of
#   these should be featured" — so every pin carrying their reviews
#   is featured: 1239 PA West Mifflin (Portals of Fear, review
#   attached below), 5728 PA Kennywood Phantom Fall Fest (two videos
#   attached below), 5967 OH Cedar Point HalloWeekends (review
#   attached below), 6095 PA Monongahela (Triple B Farms Fall
#   Festival, posted today with their review as its media), 6097 PA
#   Monroeville (The Living Dead Museum, posted today with their
#   review as its media). Pin 1641 (Hundred Acres Manor) carries
#   two of their videos and was featured by the burst ship above.
#   Featured only — the hand-picked list is untouched.)
#   6093 TN Knoxville (Oct 27: the FIRST hotels pin — Hyatt Place
#   Knoxville/Downtown, 530 S Gay St, the historic 1919 Farragut
#   Hotel building, via @aboveallmediasc's TikTok. Dan created the
#   hotels Tour Fuel category for this held link. Featured alone on
#   the brand-new Tennessee Hotels board. Hotels are venues: no
#   Scare-O-Meter, no vote. The hand-picked list is untouched.)
#   6094 WA Spokane (Oct 27: hotels pin #2 — The Historic Davenport
#   Hotel, 10 S Post St, via @charliesretroreality's ghost-stories
#   stay video; the haunting (Ellen McNamara, 1920) is genuinely
#   documented and the hotel runs Davenport After Dark tours.
#   Featured alone on the brand-new Washington Hotels board. The
#   hand-picked list is untouched.)
#   6102 BC Abbotsford (Oct 27: CANADA OPENS — Maan Farms'
#   Halloween Fright Festival, 790 McKenzie Road; HauntMap's
#   first Canadian pin, posted with @maanfarms' own TikTok on
#   Dan's explicit freshness override + Canada order. Featured
#   so it leads the new British Columbia board. Featured only —
#   the hand-picked list is untouched.)
#   6105 UK Betws-y-Coed (Oct 27: Dan's "All top 10" burst pick —
#   @zipworld's own TikTok, posted today as pin 6105 in events.


#   6106 IL Buffalo Grove (Oct 27: Dan's OVERRIDE — Scare Worth
#   Manor, 1138 Lockwood Court W; the Worth family's clown home
#   haunt from @scareworthmanor's own TikTok. Posted today as pin
#   6106 under Dan's explicit freshness override (the video is
#   from Oct 2022 and no 2026 operation is verified — Dan ruled
#   to post it anyway). Featured only — the hand-picked list is
#   untouched.)
#   1996 KY Louisville (Oct 27: Dan's "All top 10" burst pick —
#   Halloween on Hillcrest, 301 Hillcrest Ave; the pin already
#   existed with no video, so no duplicate was posted and
#   @geras88jerry's TikTok was attached to it below. Featured
#   only — the hand-picked list is untouched.)
#   6104 + 6108 CA Chino (Oct 27: Dan's "All top 10" burst pick —
#   Dan captioned the link "Recanted House encino CA", a garbled
#   dictation of "haunted houses in Chino, CA": @explorewithcourt's
#   TikTok tours TWO free Chino home haunts, posted today as two
#   pins sharing the one video per the one-pin-per-house rule —
#   6104 Dread Town, 6542 Germantown Ct (Dr. Dready's manor yard
#   haunt, 8th year), and 6108 Rotten Realms, 12850 17th St
#   (mineshaft-to-farmhouse walk-through). Featured only — the
#   hand-picked list is untouched.)
#   6107 CA Idyllwild (Oct 27: Dan's "All top 10" burst pick —
#   hotels pin #3, Hicksville Pines, 23493 CA-243, via
#   @byvanessadaily's tour of its Haunted Mansion room in the
#   Blue Chalet. Featured alone on the brand-new California
#   Hotels board. Hotels are venues: no Scare-O-Meter, no vote.
#   The hand-picked list is untouched.)
#   5950 NY New York City (Oct 27: Dan's explicit call — the NYC
#   Village Halloween Parade, Sixth Avenue, Sat Oct 31 7pm, FREE;
#   the city's flagship Halloween event. It already carried its
#   2026 edition (posted Oct 26) but was unfeatured, so it missed
#   the New York Events Top 10 entirely. Dan tapped "Feature the
#   Village Parade on NY Events Top 10" — it joins this set for
#   the New York events board. Featured only — the hand-picked
#   list is untouched.)
FEATURED_ENTRY_IDS = (5541, 5542, 5551, 5584, 5587, 5175, 4370, 5653, 5654, 5655, 5766, 5572, 5940, 6006, 116, 6084, 4932, 6085, 6087, 6088, 6086, 6090, 6089, 6091, 30, 6098, 6096, 1641, 6092, 6100, 6099, 6101, 1239, 5728, 5967, 6095, 6097, 6093, 6094, 6102, 6103, 6105, 6106, 1996, 6104, 6108, 6107, 4268, 3983, 3992, 3997, 4004, 4193, 4677, 5966, 5970, 6109, 6110, 6111, 6112, 6113, 6114, 5950, 6226)
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
# Oct 27 addition: 6005 (Pittsburgh PA) — Jonas Brothers — Live,
# @nycthrasher's live room, posted Oct 26 on Dan's hold-until-live
# instruction. Dan (Oct 27): "Move Jonas Brothers to #1 on the Live
# board." As the newest hand-picked pin it leads the live category;
# 5940 keeps its flag and follows at #2 — nothing else moves.
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
    6005,
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
    ev_venue TEXT,                        -- events facet: venue style (see EVENT_VENUES in main.py)
    virtual INTEGER NOT NULL DEFAULT 0    -- 1 = online/virtual LIVE room (Dan, Oct 27): no street address, no coords, town stored as "Online / Virtual"; live category only
);
CREATE INDEX IF NOT EXISTS idx_entries_town ON entries(town);
CREATE INDEX IF NOT EXISTS idx_entries_votes ON entries(votes DESC);
CREATE TABLE IF NOT EXISTS entry_videos (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    entry_id INTEGER NOT NULL REFERENCES entries(id) ON DELETE CASCADE,
    video_id TEXT NOT NULL,          -- TikTok video id (the dedupe key)
    url TEXT NOT NULL,               -- canonical TikTok /video/ URL
    creator TEXT,                    -- @handle parsed from the URL
    cover_path TEXT,                 -- optional per-video cover frame (site path, e.g. /static/img/tt_<id>.jpg); NULL = fall back to the pin's own thumbnail
    position INTEGER NOT NULL DEFAULT 0, -- 0 = primary; position 0 always mirrors entries.tiktok_url
    created_at TEXT NOT NULL,
    UNIQUE(entry_id, video_id)
);
CREATE INDEX IF NOT EXISTS idx_entry_videos_entry ON entry_videos(entry_id, position);
CREATE TABLE IF NOT EXISTS page_views (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    path TEXT NOT NULL,                   -- URL path visited, e.g. "/" or "/d/5"
    viewed_at TEXT NOT NULL,              -- UTC ISO timestamp
    referrer TEXT,                        -- Referer header (admin traffic stats)
    device TEXT,                          -- coarse UA bucket: iOS/Android/Windows/Mac/Linux/Other
    sid TEXT,                             -- anonymous hm_sid session cookie id
    country TEXT,                         -- Cloudflare cf-ipcountry (Oct 26 geo stats); NULL on older rows
    region TEXT,                          -- cf-ipregion: US state code when resolvable, else CF's region name; from Oct 27 also filled by the writer's IP lookup when the header is absent
    city TEXT,                            -- cf-ipcity (needs CF's visitor-location transform); NULL when absent
    user_agent TEXT,                      -- raw User-Agent header, <=512 chars (Oct 27 UA logging); NULL on older rows
    ip_addr TEXT,                         -- visitor IP as delivered by Cloudflare (cf-connecting-ip); tracker-table only, never displayed (Oct 27); NULL on older rows
    geo_src TEXT                          -- where region came from: 'cf' (Cloudflare header) | 'ip' (bundled GeoLite2 lookup); NULL when no region
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
-- Haunt Chat (Dan, Oct 27): the single members-only chat room at /chat.
-- One row per message; deleted is a soft delete so a moderator removal
-- can propagate to already-open rooms through the since-id poll (the
-- poll reports recently deleted ids alongside new messages). Frank's
-- pinned welcome is rendered from code, never a row here.
CREATE TABLE IF NOT EXISTS chat_messages (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    body TEXT NOT NULL,
    kind TEXT NOT NULL DEFAULT 'text',  -- text | sticker | poll
    reply_to INTEGER REFERENCES chat_messages(id) ON DELETE SET NULL,
    deleted INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL,
    deleted_at TEXT
);
CREATE INDEX IF NOT EXISTS idx_chat_messages_id ON chat_messages(id);
-- Haunt Chat real-time upgrade (Dan, Oct 27): treat reactions, the
-- moderation audit log + shadow-mutes, and member-vs-member word games.
-- Reactions: one row per (message, member, sticker) — re-tapping the
-- same sticker deletes the row (toggle), enforced by the primary key.
CREATE TABLE IF NOT EXISTS chat_reactions (
    message_id INTEGER NOT NULL REFERENCES chat_messages(id) ON DELETE CASCADE,
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    sticker TEXT NOT NULL,
    created_at TEXT NOT NULL,
    PRIMARY KEY (message_id, user_id, sticker)
);
CREATE INDEX IF NOT EXISTS idx_chat_reactions_msg ON chat_reactions(message_id);
-- Moderation audit log: every delete / shadow-mute / unmute / report /
-- word-filter catch lands here so admins can see who did what, when.
CREATE TABLE IF NOT EXISTS chat_mod_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    actor_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
    action TEXT NOT NULL,
    target_user_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
    message_id INTEGER,
    detail TEXT,
    created_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_chat_mod_log_id ON chat_mod_log(id);
-- Shadow-mute: a muted member's messages are stored but delivered only
-- to themselves (and admins) — no public scene, per the research brief.
CREATE TABLE IF NOT EXISTS chat_mutes (
    user_id INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    muted_by INTEGER REFERENCES users(id) ON DELETE SET NULL,
    created_at TEXT NOT NULL
);
-- Word games: one row per challenge/game. state is the game's JSON
-- state (kind-specific); status walks pending -> active -> finished,
-- with declined / expired as terminal side-exits from pending.
CREATE TABLE IF NOT EXISTS chat_games (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    kind TEXT NOT NULL,
    challenger_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    opponent_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    status TEXT NOT NULL DEFAULT 'pending',
    state TEXT NOT NULL DEFAULT '{}',
    winner_id INTEGER REFERENCES users(id) ON DELETE SET NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    expires_at TEXT
);
CREATE INDEX IF NOT EXISTS idx_chat_games_status ON chat_games(status, id);
-- Haunt Chat Wave 0 quick wins (Dan, Oct 27 — benchmark brief §4):
-- @mentions, room polls. (Reply/quote rides chat_messages.reply_to;
-- pin-a-message rides social_meta; sticker sends ride kind='sticker'.)
-- Mentions persist so a member who was offline still finds them in
-- the mentions panel; seen flips when they open it.
CREATE TABLE IF NOT EXISTS chat_mentions (
    message_id INTEGER NOT NULL REFERENCES chat_messages(id) ON DELETE CASCADE,
    mentioned_user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    seen INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL,
    PRIMARY KEY (message_id, mentioned_user_id)
);
CREATE INDEX IF NOT EXISTS idx_chat_mentions_user
    ON chat_mentions(mentioned_user_id, seen, message_id);
-- Room polls: one row per poll; the poll also lives in the room as a
-- chat_messages row of kind='poll' (message_id) so ordering, catch-up
-- and the teaser treat it like any message. Options are a JSON list.
CREATE TABLE IF NOT EXISTS chat_polls (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    message_id INTEGER REFERENCES chat_messages(id) ON DELETE CASCADE,
    question TEXT NOT NULL,
    options TEXT NOT NULL,
    created_by INTEGER REFERENCES users(id) ON DELETE SET NULL,
    closed INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL,
    closed_at TEXT
);
CREATE TABLE IF NOT EXISTS chat_poll_votes (
    poll_id INTEGER NOT NULL REFERENCES chat_polls(id) ON DELETE CASCADE,
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    option_idx INTEGER NOT NULL,
    created_at TEXT NOT NULL,
    PRIMARY KEY (poll_id, user_id)
);
-- Per-member, per-game win/loss tally rendered on HauntSocial profiles.
CREATE TABLE IF NOT EXISTS chat_game_tallies (
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    kind TEXT NOT NULL,
    wins INTEGER NOT NULL DEFAULT 0,
    losses INTEGER NOT NULL DEFAULT 0,
    PRIMARY KEY (user_id, kind)
);
-- Haunt Chat Wave 1 (Dan, Oct 27 — benchmark brief §4 headline #1):
-- Web Push + PWA. One row per browser/device subscription a member
-- has granted (endpoint is the push service's unique URL); a member
-- can have several devices. Dead endpoints (404/410 from the push
-- service) are pruned at send time.
CREATE TABLE IF NOT EXISTS push_subscriptions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    endpoint TEXT NOT NULL UNIQUE,
    p256dh TEXT NOT NULL,
    auth TEXT NOT NULL,
    user_agent TEXT,
    created_at TEXT NOT NULL,
    last_seen_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_push_subs_user
    ON push_subscriptions(user_id);
-- Per-member notification preferences. The master switch defaults
-- OFF (opt-in only, brief §4); the per-type switches default ON so
-- that turning the master on once enables the full set, and a member
-- can then mute individual types. No row = all defaults.
CREATE TABLE IF NOT EXISTS push_settings (
    user_id INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
    enabled INTEGER NOT NULL DEFAULT 0,
    mentions INTEGER NOT NULL DEFAULT 1,
    challenges INTEGER NOT NULL DEFAULT 1,
    frank INTEGER NOT NULL DEFAULT 1,
    replies INTEGER NOT NULL DEFAULT 1,
    updated_at TEXT NOT NULL
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


# ------------------------------------------------------- entry videos
# Multi-video pins (Dan, Oct 27): every video of a place lives on that
# place's ONE pin. entry_videos is the full ordered list; position 0 is
# the primary and always mirrors entries.tiktok_url, which stays the
# field boards / cards / search read (zero behaviour change for the
# one-video pins that make up nearly the whole site).

def tiktok_video_id(url: str | None) -> str | None:
    """The numeric video id in a TikTok /video/ URL, else None."""
    if not url or "/video/" not in url:
        return None
    vid = url.split("/video/", 1)[1].split("?")[0].split("/")[0].strip()
    return vid or None


def tiktok_creator(url: str | None) -> str | None:
    """The @handle in a TikTok URL, else None."""
    if not url or "/@" not in url:
        return None
    handle = url.split("/@", 1)[1].split("/")[0].split("?")[0].strip()
    return handle or None


def get_entry_videos(conn: sqlite3.Connection, entry_id: int) -> list[dict]:
    """An entry's videos, primary first (position order)."""
    rows = conn.execute(
        "SELECT * FROM entry_videos WHERE entry_id = ? ORDER BY position, id",
        (entry_id,),
    ).fetchall()
    return [dict(r) for r in rows]


def _renumber_entry_videos(conn: sqlite3.Connection, entry_id: int) -> None:
    rows = conn.execute(
        "SELECT id FROM entry_videos WHERE entry_id = ? ORDER BY position, id",
        (entry_id,),
    ).fetchall()
    for pos, r in enumerate(rows):
        conn.execute(
            "UPDATE entry_videos SET position = ? WHERE id = ?", (pos, r["id"])
        )


def _insert_entry_video(conn: sqlite3.Connection, entry_id: int, url: str,
                        position: int, cover_path: str | None = None) -> None:
    conn.execute(
        "INSERT INTO entry_videos "
        "(entry_id, video_id, url, creator, cover_path, position, created_at) "
        "VALUES (?, ?, ?, ?, ?, ?, ?)",
        (entry_id, tiktok_video_id(url), url, tiktok_creator(url), cover_path,
         position, datetime.now(timezone.utc).isoformat()),
    )


def add_entry_video(conn: sqlite3.Connection, entry_id: int, url: str,
                    cover_path: str | None = None) -> bool:
    """Append a TikTok video to an entry's list. Dedupe by video id —
    re-adding a video the pin already carries is a no-op (False).

    First video of an entry whose entries.tiktok_url is empty also
    fills that primary mirror (fill-if-empty, the pin-116 rule: an
    existing primary is never overwritten). If the entry has a primary
    but no list yet, the primary is seeded as position 0 before the
    append. Appends never touch entries.tiktok_url otherwise."""
    vid = tiktok_video_id(url)
    if not vid:
        return False
    row = conn.execute(
        "SELECT tiktok_url FROM entries WHERE id = ?", (entry_id,)
    ).fetchone()
    if row is None:
        return False
    videos = get_entry_videos(conn, entry_id)
    if any(v["video_id"] == vid for v in videos):
        return False
    if not videos:
        primary = (row["tiktok_url"] or "").strip()
        pid = tiktok_video_id(primary)
        if pid and pid != vid:
            _insert_entry_video(conn, entry_id, primary, 0)
            videos = get_entry_videos(conn, entry_id)
        elif not pid:
            conn.execute(
                "UPDATE entries SET tiktok_url = ? WHERE id = ?", (url, entry_id)
            )
    _insert_entry_video(conn, entry_id, url, len(videos), cover_path)
    return True


def set_entry_primary_video(conn: sqlite3.Connection, entry_id: int,
                            url: str | None) -> None:
    """Re-sync entry_videos after an admin edit of entries.tiktok_url.

    A /video/ URL becomes position 0 (the previous primary row is
    replaced; the rest of the list keeps its order behind it). An
    empty value clears the pin's whole video list — the admin-edit
    mental model is still "the pin's TikTok", singular. Either way
    entries.tiktok_url ends as the position-0 mirror."""
    if url:
        url = url.strip() or None
    vid = tiktok_video_id(url)
    if vid is None:
        if url:
            # Non-video TikTok URL (e.g. a live room): it lives only in
            # the mirror — the video list is not embeddable-video data.
            conn.execute(
                "UPDATE entries SET tiktok_url = ? WHERE id = ?", (url, entry_id)
            )
            return
        conn.execute("DELETE FROM entry_videos WHERE entry_id = ?", (entry_id,))
        conn.execute(
            "UPDATE entries SET tiktok_url = NULL WHERE id = ?", (entry_id,)
        )
        return
    conn.execute(
        "DELETE FROM entry_videos WHERE entry_id = ? AND position = 0",
        (entry_id,),
    )
    conn.execute(
        "DELETE FROM entry_videos WHERE entry_id = ? AND video_id = ?",
        (entry_id, vid),
    )
    _insert_entry_video(conn, entry_id, url, 0)
    _renumber_entry_videos(conn, entry_id)
    conn.execute(
        "UPDATE entries SET tiktok_url = ? WHERE id = ?", (url, entry_id)
    )


def init_db(db_path: Path) -> None:
    db_path.parent.mkdir(parents=True, exist_ok=True)
    with get_conn(db_path) as conn:
        conn.executescript(SCHEMA)
        # Haunt Chat games opt-out (Oct 27): profiles predating the
        # chat-games build gain the "don't receive game challenges" flag.
        pcols = {r["name"] for r in conn.execute("PRAGMA table_info(profiles)").fetchall()}
        if "no_challenges" not in pcols:
            conn.execute(
                "ALTER TABLE profiles ADD COLUMN no_challenges INTEGER NOT NULL DEFAULT 0"
            )
        # Haunt Chat Wave 0 (Oct 27): DBs created before the quick-win
        # build gain the message kind + reply pointer in place.
        mcols = {r["name"] for r in conn.execute("PRAGMA table_info(chat_messages)").fetchall()}
        if mcols and "kind" not in mcols:
            conn.execute(
                "ALTER TABLE chat_messages ADD COLUMN kind TEXT NOT NULL DEFAULT 'text'"
            )
        if mcols and "reply_to" not in mcols:
            conn.execute(
                "ALTER TABLE chat_messages ADD COLUMN reply_to INTEGER"
            )
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
        if "virtual" not in cols:
            # Virtual LIVE rooms (Dan, Oct 27): a category='live' entry
            # that is an online-only room (e.g. a TikTok quiz stream)
            # may post with NO street address and NO coordinates; its
            # town is stored as "Online / Virtual". The exemption is
            # scoped to live+virtual in the /upload handler — every
            # other category keeps the street-address mandate.
            conn.execute(
                "ALTER TABLE entries ADD COLUMN virtual INTEGER NOT NULL DEFAULT 0"
            )
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
        # Dan-sent video attach (Oct 27): @suzebauer's TikTok of the
        # Great Jack O'Lantern Blaze belongs on the Blaze's one pin
        # (116) — the standing one-pin-per-place rule. Fill-if-empty
        # only: an admin-set tiktok_url is never overwritten, and once
        # the pin carries any video this is a no-op.
        conn.execute(
            "UPDATE entries SET tiktok_url = ? "
            "WHERE id = 116 AND (tiktok_url IS NULL OR TRIM(tiktok_url) = '')",
            ("https://www.tiktok.com/@suzebauer/video/7691338318004440350",),
        )
        # Multi-video pins (Dan, Oct 27): backfill entry_videos from the
        # existing primaries — every entry's current tiktok_url becomes
        # position 0 of its list. The UNIQUE(entry_id, video_id) key +
        # INSERT OR IGNORE make later boots no-ops; entries.tiktok_url
        # itself is untouched (it stays the primary mirror).
        for r in conn.execute(
                "SELECT id, tiktok_url, created_at FROM entries "
                "WHERE tiktok_url LIKE '%/video/%'").fetchall():
            vid = tiktok_video_id(r["tiktok_url"])
            if not vid:
                continue
            conn.execute(
                "INSERT OR IGNORE INTO entry_videos "
                "(entry_id, video_id, url, creator, cover_path, position, created_at) "
                "VALUES (?, ?, ?, ?, NULL, 0, ?)",
                (r["id"], vid, r["tiktok_url"],
                 tiktok_creator(r["tiktok_url"]), r["created_at"]),
            )
        # Dan-sent video append (Oct 27): Al Chile's OWN TikTok joins
        # its one pin (5974) as a second video — @nayecorea00's video
        # stays primary (it was there first). add_entry_video dedupes
        # by video id, so repeat boots are no-ops and the primary is
        # never touched.
        add_entry_video(
            conn, 5974,
            "https://www.tiktok.com/@alchilebarmexican/video/7695615821242027277",
        )
        # Dan-sent video attach (Oct 27): Gloomy Oaks Manor's own
        # TikTok joins its one pin (4932) — the standing
        # one-pin-per-place rule. The pin carried no video, so
        # add_entry_video fills the empty primary mirror
        # (fill-if-empty) and lists the video at position 0; it
        # dedupes by video id, so repeat boots are no-ops.
        add_entry_video(
            conn, 4932,
            "https://www.tiktok.com/@gloomyoaksmanor/video/7699268436223905038",
        )
        # Dan-sent video append (Oct 27): @boosandbubbly's Mortem Manor
        # tour (posted Oct 2, 2026) joins its one pin (6085, Mortem
        # Manor, 5770 W Irlo Bronson Memorial Hwy, Kissimmee FL) as a
        # second video — @hiddenshorestravel's video stays primary.
        # add_entry_video dedupes by video id, so repeat boots are
        # no-ops and the primary is never touched.
        add_entry_video(
            conn, 6085,
            "https://www.tiktok.com/@boosandbubbly/video/7692137070936018207",
        )
        # Dan-sent video append (Oct 27): @freaks_of_hhn's Mortem Manor
        # visit (posted Oct 21, 2026) joins its one pin (6085) as a
        # third video — @hiddenshorestravel's video stays primary.
        # add_entry_video dedupes by video id, so repeat boots are
        # no-ops and the primary is never touched.
        add_entry_video(
            conn, 6085,
            "https://www.tiktok.com/@freaks_of_hhn/video/7698953629817900302",
        )
        # @freaks_of_hhn featured-review batch (Dan, Oct 27): Dan sent
        # the Freaks of HHN account itself (730K followers, haunt
        # reviews) with the standing dreadalertmedia treatment — "all
        # of these should be featured, they do reviews." Their 40 most
        # recent/relevant place videos (Oct 16-27, 2026) join each
        # place's ONE pin below; six places that had no pin were
        # created first via /upload (6109 Fear Reach Scream Park,
        # 6110 Dr. Grimley's Haunted Trail, 6111 Ominous Descent,
        # 6112 Fright Fest at Six Flags Over Georgia, 6113 Dark Harbor,
        # 6114 Jurassic Haunt) and carry their Freaks video as the
        # uploaded primary — only their SECOND videos appear here.
        # Every pin in this table also joins FEATURED_ENTRY_IDS above.
        # add_entry_video dedupes by video id, so repeat boots are
        # no-ops and no primary is ever touched.
        for _pin_id, _pin_urls in (
            # Halloween Horror Nights — Universal Orlando (3983)
            (3983, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7700351818836004110",
                "https://www.tiktok.com/@freaks_of_hhn/video/7700023745154403598",
                "https://www.tiktok.com/@freaks_of_hhn/video/7699925351530499342",
                "https://www.tiktok.com/@freaks_of_hhn/video/7699561525173832974",
                "https://www.tiktok.com/@freaks_of_hhn/video/7698073901993135373",
                "https://www.tiktok.com/@freaks_of_hhn/video/7698038478898056462",
                "https://www.tiktok.com/@freaks_of_hhn/video/7697782097062137102",
            )),
            # Howl-O-Scream — SeaWorld Orlando (3992)
            (3992, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7701140016449326349",
                "https://www.tiktok.com/@freaks_of_hhn/video/7700009372511898893",
                "https://www.tiktok.com/@freaks_of_hhn/video/7699582267038928142",
                "https://www.tiktok.com/@freaks_of_hhn/video/7699335000402955533",
                "https://www.tiktok.com/@freaks_of_hhn/video/7698450110878862606",
                "https://www.tiktok.com/@freaks_of_hhn/video/7698224339266571534",
                "https://www.tiktok.com/@freaks_of_hhn/video/7698219338280520974",
            )),
            # Howl-O-Scream — Busch Gardens Tampa (3997)
            (3997, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7701194510453247246",
                "https://www.tiktok.com/@freaks_of_hhn/video/7699943559440420109",
                "https://www.tiktok.com/@freaks_of_hhn/video/7699189661574483213",
                "https://www.tiktok.com/@freaks_of_hhn/video/7697747241267744014",
            )),
            # Sir Henry's Haunted Trail (4004)
            (4004, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7701470511464762637",
                "https://www.tiktok.com/@freaks_of_hhn/video/7700034910081256718",
            )),
            # Night Creepers Haunted House (4193)
            (4193, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7701026245923917070",
                "https://www.tiktok.com/@freaks_of_hhn/video/7697412135931923725",
            )),
            # The Horrorland Scream Park, Miami (4677)
            (4677, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7698971431849184526",
                "https://www.tiktok.com/@freaks_of_hhn/video/7698061558835842318",
            )),
            # Mickey's Not-So-Scary Halloween Party (5966)
            (5966, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7701096238598393101",
                "https://www.tiktok.com/@freaks_of_hhn/video/7701033563596115213",
            )),
            # Knott's Scary Farm (5970)
            (5970, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7699177879350906125",
                "https://www.tiktok.com/@freaks_of_hhn/video/7697805155185528077",
            )),
            # Halloween Horror Nights — Universal Studios Hollywood (6090)
            (6090, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7699643125119208718",
                "https://www.tiktok.com/@freaks_of_hhn/video/7698976494063799565",
                "https://www.tiktok.com/@freaks_of_hhn/video/7697834848022613261",
            )),
            # Fear Reach Scream Park (6109) — second video
            (6109, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7701085429092650253",
            )),
            # Dr. Grimley's Haunted Trail (6110) — second video
            (6110, (
                "https://www.tiktok.com/@freaks_of_hhn/video/7701031724951555342",
            )),
        ):
            for _pin_url in _pin_urls:
                add_entry_video(conn, _pin_id, _pin_url)
        # Dan-sent video attach (Oct 27): @growingwithju's TikTok of
        # the Ridgewood Halloween House (294 West End Ave, Ridgewood
        # NJ — posted Oct 11, 2026) joins its one pin (30) — the
        # standing one-pin-per-place rule. The pin carried no video,
        # so add_entry_video fills the empty primary mirror
        # (fill-if-empty) and lists the video at position 0; it
        # dedupes by video id, so repeat boots are no-ops.
        add_entry_video(
            conn, 30,
            "https://www.tiktok.com/@growingwithju/video/7695491140866428174",
        )
        # Dan-sent video append (Oct 27): @hownola's Ghost Manor
        # video (posted Oct 23, 2026) joins its one pin (6088, Ghost
        # Manor, 2502 Magazine St, New Orleans LA) as a second video —
        # @closetsamples' video stays primary. add_entry_video dedupes
        # by video id, so repeat boots are no-ops and the primary is
        # never touched. Cover is the video's own frame.
        add_entry_video(
            conn, 6088,
            "https://www.tiktok.com/@hownola/video/7699937273437015309",
            "/static/img/tt_7699937273437015309.jpg",
        )
        # Pin 6088 coords correction (Oct 27): its upload geocode
        # landed on the north shore (30.4306, -90.4171), ~38 mi from
        # the verified address point — Nominatim and Google place
        # data agree 2502 Magazine St is 29.9273, -90.0800. Guarded
        # to the bad pair so it fires once and never overrides a
        # later admin-set position.
        conn.execute(
            "UPDATE entries SET lat = ?, lng = ? WHERE id = 6088 "
            "AND ABS(lat - 30.430578882834343) < 0.001 "
            "AND ABS(lng + 90.41706556462721) < 0.001",
            (29.9272990, -90.0799994),
        )
        # Dan-sent video attach (Oct 27): @dreadalertmedia's TikTok
        # review of Hundred Acres Manor (video 7695878638356516127,
        # Oct 13 2026 — a ranking of the manor's five haunted
        # attractions) joins its one pin (1641) — the standing
        # one-pin-per-place rule. The pin carried no video, so
        # add_entry_video fills the empty primary mirror
        # (fill-if-empty) and lists the video at position 0; it
        # dedupes by video id, so repeat boots are no-ops. (The
        # halloween-category pin 1250 carries this place's name too
        # but at a wrong address — 2919 South Park Rd is an
        # auto-parts store — so the video does NOT go there; 1250
        # is left untouched for a separate merge/cleanup call.)
        add_entry_video(
            conn, 1641,
            "https://www.tiktok.com/@dreadalertmedia/video/7695878638356516127",
        )
        # Dread Alert Media review attaches (Oct 27): Dan named the
        # haunt-review account @dreadalertmedia ("Dread Alert | Horror
        # Reviews") a featured review partner — their review videos
        # join the one pin of each place they reviewed (the standing
        # one-pin-per-place rule). Pins 1239 / 5728 / 5967 carried no
        # video, so add_entry_video fills each empty primary mirror
        # (fill-if-empty) and lists the video at position 0; Kennywood
        # (5728) gets its second video appended behind the review, and
        # Hundred Acres Manor (1641) gets their earlier solo review
        # appended behind the ranking video attached above.
        # add_entry_video dedupes by video id, so repeat boots are
        # no-ops and primaries are never touched.
        add_entry_video(
            conn, 1239,
            "https://www.tiktok.com/@dreadalertmedia/video/7698447615590976798",
        )
        add_entry_video(
            conn, 1641,
            "https://www.tiktok.com/@dreadalertmedia/video/7684659895399992607",
        )
        add_entry_video(
            conn, 5728,
            "https://www.tiktok.com/@dreadalertmedia/video/7691015638931868959",
        )
        add_entry_video(
            conn, 5728,
            "https://www.tiktok.com/@dreadalertmedia/video/7682227810726874398",
        )
        add_entry_video(
            conn, 5967,
            "https://www.tiktok.com/@dreadalertmedia/video/7688108507312311583",
        )
        # Dan-sent video attach (Oct 27): @geras88jerry's Halloween on
        # Hillcrest TikTok (posted Oct 27, 2026) joins its one pin
        # (1996, Halloween on Hillcrest, 301 Hillcrest Ave, Louisville
        # KY) — the standing one-pin-per-place rule. The pin carried
        # no video, so add_entry_video fills the empty primary mirror
        # (fill-if-empty) and lists the video at position 0; it
        # dedupes by video id, so repeat boots are no-ops. Dan also
        # featured the pin (FEATURED_ENTRY_IDS) for the Kentucky
        # Halloween Top 10 — his "All top 10" burst directive.
        add_entry_video(
            conn, 1996,
            "https://www.tiktok.com/@geras88jerry/video/7701197521317563666",
        )
        # Dan-sent video attach (Oct 27): @ninjamomm's TikTok of The
        # Escondido Madhouse (posted Oct 25, 2026 — she calls it the
        # coolest haunted house she has ever seen; the haunt is open
        # Oct 31) joins its one pin (4268, 10275 Spruce Woodlands Way,
        # Escondido CA — the FrightMaps-imported pin already carried
        # the verified address, exact-house coords and a photo, but
        # no video) — the standing one-pin-per-place rule. The pin
        # carried no video, so add_entry_video fills the empty
        # primary mirror (fill-if-empty) and lists the video at
        # position 0; it dedupes by video id, so repeat boots are
        # no-ops. (A fresh /upload for this place was attempted first
        # and correctly rejected/dupe-avoided: the address geocodes
        # only under OSM's "Hidden Meadows" locality and the place
        # already had its pin.) Pin 4268 joins FEATURED_ENTRY_IDS
        # for the California Halloween Top 10 — Dan's "All top 10"
        # burst directive; ranking data untouched.
        add_entry_video(
            conn, 4268,
            "https://www.tiktok.com/@ninjamomm/video/7700668531167350047",
        )
        # batch02 backlog appends (Oct 28): Dan's "post the 153 batch"
        # run — second videos of places whose pins already carry a
        # primary join their one pin (the standing one-pin-per-place
        # rule). Primaries were filled first via /admin/edit where the
        # pin had none (33, 45, 49, 331, 337, 1967); pins 30 and 174
        # already had primaries. add_entry_video dedupes by video id,
        # so repeat boots are no-ops and primaries are never touched.
        add_entry_video(
            conn, 30,
            "https://www.tiktok.com/@lilroamingexplorers/video/7695744716171726111",
        )
        add_entry_video(
            conn, 33,
            "https://www.tiktok.com/@lilroamingexplorers/video/7693949903176879391",
        )
        add_entry_video(
            conn, 45,
            "https://www.tiktok.com/@holiday.houses.on.li/video/7698220441479007502",
        )
        add_entry_video(
            conn, 49,
            "https://www.tiktok.com/@holiday.houses.on.li/video/7695028746406874398",
        )
        add_entry_video(
            conn, 174,
            "https://www.tiktok.com/@palmeravenuehaunt/video/7698864687143849247",
        )
        add_entry_video(
            conn, 331,
            "https://www.tiktok.com/@holiday.houses.on.li/video/7692603341339135246",
        )
        add_entry_video(
            conn, 337,
            "https://www.tiktok.com/@5thstreethaunt/video/7696003645413838094",
        )
        add_entry_video(
            conn, 337,
            "https://www.tiktok.com/@5thstreethaunt/video/7697738366917365006",
        )
        add_entry_video(
            conn, 1967,
            "https://www.tiktok.com/@roroaming/video/7699565270209269022",
        )
        # batch02 appends behind SHORT-LINK primaries (Oct 28): pins
        # 177 and 813 store their primary as a tiktok.com/t/ short
        # link, which has no /video/ id — add_entry_video would treat
        # the pin as video-less and replace the mirror. Seed the
        # resolved primary first (same video: 177 = @thekaylamurphy
        # 7693715642515557645 via t/ZPLAe91oE; 813 = @anniedoescomedy
        # 7698211947409444110 via t/ZPLARyN9E), then append.
        add_entry_video(
            conn, 177,
            "https://www.tiktok.com/@thekaylamurphy/video/7693715642515557645",
        )
        add_entry_video(
            conn, 177,
            "https://www.tiktok.com/@holiday.houses.on.li/video/7700334366261595405",
        )
        add_entry_video(
            conn, 813,
            "https://www.tiktok.com/@anniedoescomedy/video/7698211947409444110",
        )
        add_entry_video(
            conn, 813,
            "https://www.tiktok.com/@afrazexplores/video/7695873448731528461",
        )
        # Dan-sent video append (Oct 28): @kikegonzaleznj's Clinton
        # Place street tour (video 7701136015599127822, posted Oct 26
        # ET 2026 — a Spanish-language walk down Clinton Place,
        # Hackensack NJ: giant skeletons, clowns and full yard scenes
        # house after house) joins the street's roundup pin (32,
        # "Clinton Place — 2 Blocks of Houses", anchored 14 Clinton
        # Place) — the video tours the whole street, so it rides the
        # street pin, not the single-house pins (551/552) and not the
        # second street pin (666). The pin carried no video, so
        # add_entry_video fills the empty primary mirror
        # (fill-if-empty) and lists the video at position 0; it
        # dedupes by video id, so repeat boots are no-ops. Cover is
        # the video's own frame.
        add_entry_video(
            conn, 32,
            "https://www.tiktok.com/@kikegonzaleznj/video/7701136015599127822",
            "/static/img/tt_7701136015599127822.jpg",
        )
        # Dan-sent video appends (Oct 28): @lilroamingexplorers'
        # "7 North Jersey Halloween Houses" roundup (video
        # 7701720133693099295, posted Oct 28, 2026) names seven free
        # displays; five of them already have their one pin, so the
        # video joins those pins (standing one-pin-per-place rule)
        # instead of creating duplicates:
        #   340 — 47 Glenmere Terrace, Mahwah (the earlier of the
        #         340/624 duplicate pair; twin left for Dan's cleanup)
        #   691 — 499 Island Way, Franklin Lakes (earlier of 691/719)
        #   322 — 27 Brooklake Rd, Florham Park (earlier of 322/588)
        #   3213 — Hallows Gate Cemetery, 28 Esplanade Drive,
        #         Hillsdale (the caption's street-only "Esplanade
        #         Drive, Hillsdale" entry — the street's listed
        #         display; the number is confirmed by the pin itself)
        #   24 — Morse Avenue Manor, 41 Morse Ave, Bloomfield (the
        #         caption's "Morse Ave Manor"; number confirmed by
        #         the pin; appends behind the existing
        #         @joanowholidaydisplays primary)
        # The two roundup houses with no pin (162 Lake Ave, Clifton
        # and 92 Monroe Street, Cedar Grove) were posted fresh via
        # /upload as pins 6621/6622 with the video as primary.
        # Pins 340/691/322/3213 carried no video, so add_entry_video
        # fills each empty primary mirror (fill-if-empty) and lists
        # the video at position 0; it dedupes by video id, so
        # repeat boots are no-ops.
        add_entry_video(
            conn, 340,
            "https://www.tiktok.com/@lilroamingexplorers/video/7701720133693099295",
        )
        add_entry_video(
            conn, 691,
            "https://www.tiktok.com/@lilroamingexplorers/video/7701720133693099295",
        )
        add_entry_video(
            conn, 322,
            "https://www.tiktok.com/@lilroamingexplorers/video/7701720133693099295",
        )
        add_entry_video(
            conn, 3213,
            "https://www.tiktok.com/@lilroamingexplorers/video/7701720133693099295",
        )
        add_entry_video(
            conn, 24,
            "https://www.tiktok.com/@lilroamingexplorers/video/7701720133693099295",
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
        # Raw User-Agent per page view (Dan, Oct 27): the device bucket
        # alone can't separate bot families (Googlebot vs TikTok /
        # iMessage link previews vs uptime monitors), which the Oct 27
        # machine-traffic breakdown flagged as the blind spot in sponsor
        # reporting. Additive only — no counting query reads this column,
        # so every published figure is unchanged. Same startup-ensure
        # pattern; older rows stay NULL.
        if "user_agent" not in pvcols:
            conn.execute("ALTER TABLE page_views ADD COLUMN user_agent TEXT")
        # Visitor IP + region source (Dan, Oct 27): ip_addr is the
        # visitor address as delivered by Cloudflare (cf-connecting-ip),
        # stored in this tracker table only and never displayed — the
        # analytics writer resolves a U.S. state from it against the
        # bundled GeoLite2 database when Cloudflare's headers carry no
        # region, and geo_src records where the region came from
        # ('cf' | 'ip'). Same startup-ensure pattern; older rows NULL.
        for col in ("ip_addr", "geo_src"):
            if col not in pvcols:
                conn.execute(f"ALTER TABLE page_views ADD COLUMN {col} TEXT")
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
