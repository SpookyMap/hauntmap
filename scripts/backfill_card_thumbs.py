#!/usr/bin/env python3
"""Backfill 480-wide feed-card thumbnail variants (Retention Wave 6, Item 10).

Full feed thumbs are 800x600 JPEGs (mean ~65 KB on the Oct 23 snapshot)
while phone cards render ~380 px wide. The card variant is the same
image at 480x360, JPEG q76 — same filename, in the sibling subdir
``thumbs/card/`` under the uploads dir, so it is served by the existing
/media static mount at ``/media/thumbs/card/<same filename>``.

Templates use the variant ONLY for feed cards (see
``thumb_card_url`` in app/main.py, which checks the variant file
exists and falls back to the full thumb when it does not — plus an
``onerror`` swap in the card templates as a second net). Detail-page
hero imagery keeps the full-size thumb.

Usage:
  python scripts/backfill_card_thumbs.py [--uploads DIR] [--force]

  --uploads  uploads directory containing thumbs/ (default:
             $UPLOAD_DIR, else ./uploads next to the repo root layout,
             else ~/workspace/hauntmap-retention-data/uploads)
  --force    regenerate even when a variant already exists and is
             newer than its source thumb

Idempotent: existing up-to-date variants are skipped. Exits non-zero
only on a usage error; per-file failures are counted, never fatal.
This script is the deploy-day step for production: run it once
against the production uploads dir after deploying Item 10 (new
uploads generate their variant inline in make_thumb /
make_video_poster from then on).
"""
import argparse
import os
import sys
from pathlib import Path

CARD_W, CARD_H = 480, 360
JPEG_QUALITY = 76


def default_uploads() -> Path:
    env = os.environ.get("UPLOAD_DIR")
    if env:
        return Path(env)
    local = Path(__file__).resolve().parent.parent / "uploads"
    if (local / "thumbs").is_dir():
        return local
    return Path.home() / "workspace" / "hauntmap-retention-data" / "uploads"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--uploads", type=Path, default=None)
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args()
    uploads = args.uploads or default_uploads()
    thumbs = uploads / "thumbs"
    if not thumbs.is_dir():
        print(f"error: no thumbs dir at {thumbs}", file=sys.stderr)
        return 2
    card_dir = thumbs / "card"
    card_dir.mkdir(parents=True, exist_ok=True)

    from PIL import Image, ImageOps, UnidentifiedImageError

    made = skipped = failed = 0
    bytes_before = bytes_after = 0
    for src in sorted(thumbs.glob("*.jpg")):
        dest = card_dir / src.name
        try:
            if (not args.force and dest.exists()
                    and dest.stat().st_mtime >= src.stat().st_mtime):
                skipped += 1
                bytes_before += src.stat().st_size
                bytes_after += dest.stat().st_size
                continue
            with Image.open(src) as im:
                im.load()
                im = ImageOps.exif_transpose(im).convert("RGB")
                if im.size != (CARD_W, CARD_H):
                    im = im.resize((CARD_W, CARD_H), Image.LANCZOS)
                im.save(dest, "JPEG", quality=JPEG_QUALITY, optimize=True)
            made += 1
            bytes_before += src.stat().st_size
            bytes_after += dest.stat().st_size
        except (OSError, UnidentifiedImageError) as exc:
            failed += 1
            print(f"  skip {src.name}: {exc}", file=sys.stderr)
    total = made + skipped + failed
    print(f"uploads: {uploads}")
    print(f"thumbs processed: {total} (made {made}, already-ok {skipped}, failed {failed})")
    if bytes_before:
        print(f"full thumbs: {bytes_before:,} B ({bytes_before/1e6:.1f} MB, mean {bytes_before/max(total-failed,1)/1024:.1f} KB)")
        print(f"card variants: {bytes_after:,} B ({bytes_after/1e6:.1f} MB, mean {bytes_after/max(total-failed,1)/1024:.1f} KB)")
        print(f"saving: {bytes_before-bytes_after:,} B ({100*(bytes_before-bytes_after)/bytes_before:.1f}%)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
