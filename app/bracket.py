"""Haunt Bracket: America's Scariest House — staged build (Oct 2026).

Single-elimination tournament of 16 real HauntMap pins on the Haunt or Not
duel plumbing: no accounts, identity is a voter cookie (same soft-limit
pattern as the rest of the site), an IP hash is stored per vote for audit.

Seeding (Dan's approved spec, Oct 23): data-seeded from the Oct 23 03:00
production backup — seed score = pin-page views + 5 x votes + 3 x duel
wins — with geographic spread enforced (Northeast 5, Midwest 2,
Southeast 2, South/TX 2, West 4, PNW 1; no metro repeated). Pins posted
in the Oct 23 video blitz (ids 4356+) carry no accumulated stats yet;
they were seeded on video + region + display profile and are marked
"new 10/23" in SEED_NOTES. Dan holds veto/swap on every seed.

Round clock (America/New_York):
  Round of 16  Sat Oct 24 00:00 - Sun Oct 25 23:59  (all 8 matchups open
               across the window — one vote table, one window check;
               staggering would need per-matchup windows and would cut
               the Pick the Champion entry window to one day)
  Quarterfinal Mon Oct 26 - Tue Oct 27
  Semifinal    Wed Oct 28 - Thu Oct 29
  Final        Fri Oct 30 - Sat Oct 31 18:00
  Champion     crowned Halloween night, Sat Oct 31 19:00
Pick the Champion locks at the Round-of-16 close (Oct 25 23:59 ET).

BRACKET_NOW env var (ISO datetime) overrides the clock — LOCAL PREVIEW
ONLY, so staged screenshots can show in-round and crowning states with
real pins and real (zero) vote counts. Never set in production.
"""
import hashlib
import json
import os
from datetime import datetime, time, timedelta, timezone
from zoneinfo import ZoneInfo

ET = ZoneInfo("America/New_York")

# seed number -> entry id (standard 1v16, 2v15 ... ordering applied below)
SEEDS: dict[int, int] = {
    1: 111,    # 356 Connecticut Ave — Massapequa Park, NY (Northeast)
    2: 33,     # Berkeley Place — Dumont, NJ (Northeast) [video]
    3: 13,     # Hillside Ave Display — Glen Ridge, NJ (Northeast)
    4: 1,      # Spooky Ghost Yard — Hawthorne, NJ (Northeast) [video]
    5: 94,     # W 82nd St — Upper West Side, New York, NY (Northeast)
    6: 2003,   # Wilkes Family Halloween — Bensenville, IL (Midwest) [video]
    7: 927,    # Giant LEGO Skeleton — Olmsted Falls, OH (Midwest) [video]
    8: 1964,   # Burroughs Place Cemetery — Stevenson Ranch, CA (West)
    9: 3816,   # Lexington Point Haunt — Nashville, TN (Southeast)
    10: 2378,  # Groovy Ghost In Pleasant Grove — Dallas, TX (South/TX)
    11: 4381,  # Cutting Edge Haunted House — Fort Worth, TX (South/TX) [video, new 10/23]
    12: 4356,  # Hellbilly Holler — Phoenix, AZ (West) [video, new 10/23]
    13: 4369,  # Clements Haunted Hollow — Castle Rock, CO (West) [video, new 10/23]
    14: 4391,  # Hernandez Creepshow — Las Vegas, NV (West) [video, new 10/23]
    15: 4389,  # CARN-EVIL — Miami, FL (Southeast) [video, new 10/23]
    16: 4396,  # Smithing Family Lights — Kent, WA (PNW) [video, new 10/23]
}
SEED_OF = {v: k for k, v in SEEDS.items()}

REGIONS: dict[int, str] = {
    111: "Northeast", 33: "Northeast", 13: "Northeast", 1: "Northeast",
    94: "Northeast", 2003: "Midwest", 927: "Midwest", 3816: "Southeast",
    4389: "Southeast", 4381: "South / Texas", 2378: "South / Texas",
    1964: "West", 4356: "West", 4369: "West", 4391: "West", 4396: "Pacific NW",
}
HAS_VIDEO = {33, 1, 2003, 927, 4381, 4356, 4369, 4391, 4389, 4396}
# Seeding provenance from the Oct 23 03:00 production backup.
SEED_NOTES: dict[int, str] = {
    111: "49 pin views · 2 votes — #1 pin on the whole map",
    33: "37 pin views — top NJ video pin",
    13: "29 pin views",
    1: "25 pin views · video pin",
    94: "24 pin views — Manhattan's top display",
    2003: "13 pin views · video pin · Illinois anchor",
    927: "9 pin views · video pin",
    1964: "9 pin views — top West pin in the backup",
    3816: "7 pin views — top Southeast pin in the backup",
    2378: "5 pin views — top Texas photo pin in the backup",
    4381: "Posted Oct 23 video blitz — world-famous Fort Worth haunt, no stats yet",
    4356: "Posted Oct 23 video blitz — Phoenix video pick, no stats yet",
    4369: "Posted Oct 23 video blitz — Colorado video pick, no stats yet",
    4391: "Posted Oct 23 video blitz — Las Vegas video pick, no stats yet",
    4389: "Posted Oct 23 video blitz — Miami video pick, no stats yet",
    4396: "Posted Oct 23 video blitz — Pacific NW video pick, no stats yet",
}

# Round of 16 pairings in bracket order (winner of M1 meets winner of M2…)
R16_PAIRS = [(1, 16), (8, 9), (5, 12), (4, 13), (6, 11), (3, 14), (7, 10), (2, 15)]
ROUND_POINTS = {"r16": 1, "qf": 2, "sf": 4, "final": 8}
ROUND_LABELS = {"r16": "Round of 16", "qf": "Quarterfinals",
                "sf": "Semifinals", "final": "The Final"}


def _et(day: int, hh: int = 0, mm: int = 0) -> datetime:
    return datetime.combine(datetime(2026, 10, day).date(), time(hh, mm), tzinfo=ET)


ROUNDS = [
    {"key": "r16", "opens": _et(24), "closes": _et(25, 23, 59),
     "matchups": [f"M{i+1}" for i in range(8)]},
    {"key": "qf", "opens": _et(26), "closes": _et(27, 23, 59),
     "matchups": [f"QF{i+1}" for i in range(4)]},
    {"key": "sf", "opens": _et(28), "closes": _et(29, 23, 59),
     "matchups": [f"SF{i+1}" for i in range(2)]},
    {"key": "final", "opens": _et(30), "closes": _et(31, 18, 0),
     "matchups": ["F"]},
]
CROWN_AT = _et(31, 19, 0)
PREDICT_LOCK = ROUNDS[0]["closes"]  # first Round-of-16 vote close

# Which matchups feed which (for resolving pairings + prediction cascade).
FEEDS = {"QF1": ("M1", "M2"), "QF2": ("M3", "M4"), "QF3": ("M5", "M6"),
         "QF4": ("M7", "M8"), "SF1": ("QF1", "QF2"), "SF2": ("QF3", "QF4"),
         "F": ("SF1", "SF2")}
ROUND_OF = {m: "r16" for m in ROUNDS[0]["matchups"]}
ROUND_OF.update({m: "qf" for m in ROUNDS[1]["matchups"]})
ROUND_OF.update({m: "sf" for m in ROUNDS[2]["matchups"]})
ROUND_OF["F"] = "final"
ALL_MATCHUPS = [m for r in ROUNDS for m in r["matchups"]]

TABLES_SQL = """
CREATE TABLE IF NOT EXISTS bracket_votes (
    matchup_id TEXT NOT NULL,
    entry_id INTEGER NOT NULL,
    voter TEXT NOT NULL,
    ip_hash TEXT,
    created_at TEXT NOT NULL,
    PRIMARY KEY (matchup_id, voter)
);
CREATE TABLE IF NOT EXISTS bracket_winners (
    matchup_id TEXT PRIMARY KEY,
    winner_id INTEGER NOT NULL,
    resolved_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS bracket_predictions (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    voter TEXT NOT NULL UNIQUE,
    handle TEXT NOT NULL,
    contact TEXT,
    picks TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL
);
"""


def now_et() -> datetime:
    override = os.environ.get("BRACKET_NOW", "").strip()
    if override:
        try:
            dt = datetime.fromisoformat(override)
            return dt if dt.tzinfo else dt.replace(tzinfo=ET)
        except ValueError:
            pass
    return datetime.now(ET)


def phase(now: datetime | None = None) -> str:
    """pre | r16 | qf | sf | final | crowned | between"""
    now = now or now_et()
    if now >= CROWN_AT:
        return "crowned"
    for r in ROUNDS:
        if r["opens"] <= now <= r["closes"] + timedelta(minutes=1):
            return r["key"]
    if now < ROUNDS[0]["opens"]:
        return "pre"
    return "between"


def current_round(now: datetime | None = None) -> dict | None:
    now = now or now_et()
    for r in ROUNDS:
        if r["opens"] <= now <= r["closes"] + timedelta(minutes=1):
            return r
    return None


def next_milestone(now: datetime | None = None) -> tuple[str, datetime]:
    now = now or now_et()
    marks = [("Voting opens — Round of 16", ROUNDS[0]["opens"]),
             ("Predictions lock + Round of 16 closes", PREDICT_LOCK),
             ("Quarterfinals close", ROUNDS[1]["closes"]),
             ("Semifinals close", ROUNDS[2]["closes"]),
             ("Final closes", ROUNDS[3]["closes"]),
             ("Champion crowned — Halloween night", CROWN_AT)]
    for label, when in marks:
        if now < when:
            return label, when
    return "Champion crowned", CROWN_AT


def matchup_pair(matchup_id: str, winners: dict[str, int]) -> tuple[int | None, int | None]:
    """(entry_a, entry_b) for a matchup; None where a feeder is unresolved."""
    if matchup_id.startswith("M"):
        s1, s2 = R16_PAIRS[int(matchup_id[1:]) - 1]
        return SEEDS[s1], SEEDS[s2]
    f1, f2 = FEEDS[matchup_id]
    return winners.get(f1), winners.get(f2)


def get_winners(conn) -> dict[str, int]:
    conn.executescript(TABLES_SQL)
    return {r["matchup_id"]: r["winner_id"] for r in conn.execute(
        "SELECT matchup_id, winner_id FROM bracket_winners").fetchall()}


def vote_counts(conn, matchup_id: str) -> dict[int, int]:
    conn.executescript(TABLES_SQL)
    return {r["entry_id"]: r["n"] for r in conn.execute(
        "SELECT entry_id, COUNT(*) AS n FROM bracket_votes "
        "WHERE matchup_id = ? GROUP BY entry_id", (matchup_id,)).fetchall()}


def resolve_matchup(conn, matchup_id: str) -> int | None:
    """Winner = most bracket votes; ties (incl. 0-0) go to the higher seed
    (lower seed number) — the documented tiebreak. Idempotent."""
    winners = get_winners(conn)
    if matchup_id in winners:
        return winners[matchup_id]
    a, b = matchup_pair(matchup_id, winners)
    if a is None or b is None:
        return None
    counts = vote_counts(conn, matchup_id)
    ca, cb = counts.get(a, 0), counts.get(b, 0)
    if ca == cb:
        winner = a if SEED_OF[a] < SEED_OF[b] else b
    else:
        winner = a if ca > cb else b
    conn.execute(
        "INSERT OR REPLACE INTO bracket_winners (matchup_id, winner_id, resolved_at) "
        "VALUES (?, ?, ?)", (matchup_id, winner, datetime.now(timezone.utc).isoformat()))
    conn.commit()
    return winner


def prediction_score(picks: dict, winners: dict[str, int]) -> int:
    total = 0
    for matchup_id, winner in winners.items():
        if picks.get(matchup_id) == winner:
            total += ROUND_POINTS[ROUND_OF[matchup_id]]
    return total


def ip_hash(request) -> str:
    raw = (request.headers.get("x-forwarded-for", "")
           or (request.client.host if request.client else "") or "")
    return hashlib.sha256(raw.encode()).hexdigest()[:16]
