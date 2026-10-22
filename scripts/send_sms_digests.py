#!/usr/bin/env python3
"""HauntMap SMS digest sender (Dan, Oct 22) — cron-ready, capture-first.

Design: run once daily (~9 AM ET, after the daily hunt + event postings).
It looks at pins created since the watermark, builds ONE digest text per
confirmed subscriber (never more than 1/day), sends via Twilio, and logs
every send to the sms_sends table.

SAFETY: without TWILIO_ACCOUNT_SID / TWILIO_AUTH_TOKEN / TWILIO_FROM_NUMBER
in the environment this script CANNOT send — it prints what it WOULD do
for confirmed subscribers and exits without touching the watermark.
--dry-run does the same even when Twilio is configured (and also includes
'captured' subscribers, marked, so the pre-launch list can be previewed).

Watermark: sms_watermark.txt next to the DB (ISO timestamp). Advances only
after a real send pass.

Usage:
  python3 scripts/send_sms_digests.py [--db PATH] [--since ISO] [--dry-run]
Cron (once Twilio is live — do NOT install before):
  0 9 * * *  cd /path/to/hauntmap && python3 scripts/send_sms_digests.py
"""
import argparse
import os
import sqlite3
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from app import sms_alerts  # noqa: E402
from app.db import get_conn  # noqa: E402


def default_db() -> Path:
    data_dir = Path(os.environ.get("DATA_DIR",
                                   Path(__file__).resolve().parent.parent / "data"))
    return data_dir / "hauntmap.db"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", type=Path, default=default_db())
    ap.add_argument("--since", default="")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if not args.db.exists():
        print(f"DB not found: {args.db}")
        return 1
    wm_file = args.db.parent / "sms_watermark.txt"
    since = args.since
    if not since and wm_file.exists():
        since = wm_file.read_text().strip()
    if not since:
        since = (datetime.now(timezone.utc)
                 .replace(hour=0, minute=0, second=0, microsecond=0)
                 .isoformat())
    now_iso = datetime.now(timezone.utc).isoformat()

    with get_conn(args.db) as conn:
        sms_alerts.ensure_sms_tables(conn)
        pins = [dict(r) for r in conn.execute(
            "SELECT id, title, town, category, lat, lng FROM entries "
            "WHERE hidden = 0 AND created_at > ? ORDER BY id", (since,))]
        statuses = ("confirmed", "captured") if args.dry_run else ("confirmed",)
        subs = [dict(r) for r in conn.execute(
            "SELECT * FROM sms_subscribers WHERE status IN (%s)"
            % ",".join("?" * len(statuses)), statuses)]
        digests = sms_alerts.select_digests(subs, pins)
        print(f"since {since}: {len(pins)} new pins, {len(subs)} eligible "
              f"subscribers, {len(digests)} digests")

        if not sms_alerts.twilio_configured() and not args.dry_run:
            print("Twilio is NOT configured — sending disabled. "
                  "No texts sent, watermark untouched.")
            for d in digests:
                print(f"  WOULD SEND to {d['subscriber']['phone']}: "
                      f"{d['digest']}")
            return 0

        sent_today = {r["subscriber_id"] for r in conn.execute(
            "SELECT subscriber_id FROM sms_sends WHERE kind = 'digest' "
            "AND created_at >= ?", (now_iso[:10],))}
        sent = 0
        for d in digests:
            sub = d["subscriber"]
            if sub["id"] in sent_today:
                print(f"  skip {sub['phone']} — already got today's digest")
                continue
            pin_ids = ",".join(str(p["id"]) for p in d["pins"])
            if args.dry_run:
                print(f"  DRY-RUN to {sub['phone']} "
                      f"({sub['status']}): {d['digest']}")
                status = "dry_run"
                sid = ""
            else:
                try:
                    sid = sms_alerts.send_sms(sub["phone"], d["digest"])
                    status = "sent"
                    sent += 1
                except Exception as exc:  # log and move on to the next sub
                    print(f"  FAILED {sub['phone']}: {exc}")
                    sid, status = "", "failed"
            conn.execute(
                "INSERT INTO sms_sends (subscriber_id, kind, body, pin_ids, "
                "twilio_sid, status, created_at) VALUES (?, 'digest', ?, "
                "?, ?, ?, ?)",
                (sub["id"], d["digest"], pin_ids, sid, status, now_iso))
        conn.commit()

    if not args.dry_run and sms_alerts.twilio_configured():
        wm_file.write_text(now_iso)
        print(f"sent {sent} digests; watermark advanced to {now_iso}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
