#!/usr/bin/env python3
"""Dry-run for the HauntMap SMS matching engine — NO sends, NO production
writes. Proves the distance / radius / town-only / interest filtering
against real pins posted today (batch JSON records and/or a DB) using 5
SYNTHETIC test subscribers that exist only in this script's memory.

Usage:
  python3 scripts/sms_dry_run.py \
      --pins-json hidden_files/big_events_wave_2026-10-22.json [...] \
      [--db PATH --since ISO]
"""
import argparse
import json
import sqlite3
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from app import sms_alerts  # noqa: E402

# TEST DATA ONLY — never inserted anywhere. Phones use the reserved
# 555-0100..0199 fictional range.
TEST_SUBSCRIBERS = [
    {"phone": "+15550001001", "zip": "07960", "town": "Morristown",
     "state": "NJ", "radius_miles": 15, "interests": "both",
     "status": "captured",
     "label": "TEST-1 Morristown NJ — 15 mi, haunts+events"},
    {"phone": "+15550001002", "zip": "11215", "town": "Brooklyn",
     "state": "NY", "radius_miles": 10, "interests": "events",
     "status": "captured",
     "label": "TEST-2 Brooklyn NY — 10 mi, EVENTS ONLY"},
    {"phone": "+15550001003", "zip": "10591", "town": "Sleepy Hollow",
     "state": "NY", "radius_miles": 0, "interests": "both",
     "status": "captured",
     "label": "TEST-3 Sleepy Hollow NY — MY TOWN ONLY, haunts+events"},
    {"phone": "+15550001004", "zip": "78701", "town": "Austin",
     "state": "TX", "radius_miles": 25, "interests": "both",
     "status": "captured",
     "label": "TEST-4 Austin TX — 25 mi, haunts+events (far from today's pins)"},
    {"phone": "+15550001005", "zip": "10301", "town": "Staten Island",
     "state": "NY", "radius_miles": 5, "interests": "haunts",
     "status": "captured",
     "label": "TEST-5 Staten Island NY — 5 mi, HAUNTS ONLY"},
]


def load_pins_json(path: Path) -> list[dict]:
    data = json.loads(path.read_text())
    if isinstance(data, dict):
        rows = data.get("posted") or data.get("pins") or []
    else:
        rows = data
    pins = []
    for r in rows or []:
        if not isinstance(r, dict) or "id" not in r or "category" not in r:
            continue
        pins.append({"id": r["id"], "title": r.get("title", ""),
                     "town": r.get("town", ""),
                     "category": r.get("category"),
                     "lat": r.get("lat"), "lng": r.get("lng")})
    return pins


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pins-json", nargs="*", type=Path, default=[])
    ap.add_argument("--db", type=Path)
    ap.add_argument("--since", default="2026-10-22T00:00:00+00:00")
    args = ap.parse_args()

    pins: dict[int, dict] = {}
    for p in args.pins_json:
        for pin in load_pins_json(p):
            pins[pin["id"]] = pin
    if args.db and args.db.exists():
        conn = sqlite3.connect(str(args.db))
        conn.row_factory = sqlite3.Row
        for r in conn.execute(
                "SELECT id, title, town, category, lat, lng FROM entries "
                "WHERE created_at >= ?", (args.since,)):
            pins[r["id"]] = dict(r)
    pin_list = sorted(pins.values(), key=lambda p: p["id"])
    print(f"PIN POOL: {len(pin_list)} pins — "
          + ", ".join(f"{k}={v}" for k, v in
                      Counter(p['category'] for p in pin_list).most_common()))
    print("=" * 78)

    results = sms_alerts.select_digests(TEST_SUBSCRIBERS, pin_list)
    by_phone = {d["subscriber"]["phone"]: d for d in results}
    total_texts = 0
    for sub in TEST_SUBSCRIBERS:
        print(f"\n{sub['label']}  ({sub['phone']})")
        d = by_phone.get(sub["phone"])
        # Re-run per-pin to explain exclusions even when nothing matched.
        matched, excluded = [], []
        for pin in pin_list:
            ok, reason, dist = sms_alerts.match_pin(sub, pin)
            (matched if ok else excluded).append((pin, reason, dist))
        if matched:
            total_texts += 1
            for pin, reason, _ in matched:
                print(f"  MATCH  pin {pin['id']}: {pin['title'][:64]} "
                      f"[{pin['town']}] — {reason}")
            print(f"  DIGEST -> {sms_alerts.build_digest(sub, [p for p, _, _ in matched])}")
        else:
            print("  NO TEXT — nothing matched")
        reasons = Counter()
        nearest = None
        for pin, reason, dist in excluded:
            key = ("interest filter" if "wants" in reason or "not a haunt" in reason
                   else "town-only mismatch" if "town-only" in reason
                   else "outside radius" if "outside" in reason
                   else "other")
            reasons[key] += 1
            if dist is not None and (nearest is None or dist < nearest[0]):
                nearest = (dist, pin)
        print(f"  excluded: {dict(reasons)}"
              + (f"; nearest pin overall {nearest[0]:.1f} mi "
                 f"(pin {nearest[1]['id']}, {nearest[1]['town']})"
                 if nearest else ""))
    print("\n" + "=" * 78)
    print(f"TOTAL: {total_texts} digest texts would be sent "
          f"(of {len(TEST_SUBSCRIBERS)} test subscribers)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
