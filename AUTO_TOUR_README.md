# Auto Tour — STAGED PROTOTYPE (do not ship without Dan's preview)

Dan's request (Oct 27, 2026): *"add a feature to create a tour of the
top 100 and top ten in your area that takes some of the work out for
you."* Branch `auto-tour-staged`, based on origin/main 5dddb97.
Nothing here is live; stylesheet bump z176 → z177 is staged with it.

## What a visitor gets

- **Homepage entry point** — a "⚡ Build my tour for me" panel with two
  buttons, **Top 10 near me** (one night) and **Top 100 near me**
  (planned by nights). It sits directly under the Top 10 by State
  block: hero copy in the panel on laptop, twin in the phone hero grid
  (area `autotour`, under Top 10, above Follow-us-on-TikTok), exactly
  one copy visible per viewport like every other homepage module.
  A matching banner sits at the top of **/tour**.
- **/auto-tour?size=10|100** — the generated route list:
  - *Top 10*: one night, 10 stops in drive order.
  - *Top 100*: the full ranked set as one route, grouped into
    **nights of 10 consecutive route stops** (100 stops is not one
    drive). Each night shows its stops, its mileage from home, and an
    **"Open this night as a tour"** button.
- Opening a night mints a **real tour through the existing system**:
  the button POSTs the night's pin ids to the existing `/api/tours`
  (the same call the tour builder's Share button makes) and lands on
  `/t/{slug}` — map, Google Maps directions export, and "Copy this
  tour" into the builder for reordering/adding/dropping stops.
  Nothing is pre-minted; no tour row exists until a visitor taps.
  (The shared-tour cap is 50 stops, so one 100-stop tour was never an
  option — nights of 10 sit comfortably inside it.)

## How it works

- **Ranking** — identical currency to Top 10 by State and Top 100
  Nationwide: `_entries_with_views` + `_rank_with_featured`
  (detail-page views DESC, votes tiebreak, ⭐ Featured editor's picks
  guaranteed a slot; counts never altered). "Top near me" = that same
  ranking, radius-filtered.
- **Eligibility (address rule)** — a pin may enter an auto-tour only
  if it is visible, has coordinates, **and has a verified street
  address** (`entries.address` non-empty). On the Oct 26 production
  backup that filter costs almost nothing: 3,256 of 3,258 halloween
  pins qualify.
- **Radius** — Top 10 searches **25 mi** (Dan's pick, Oct 27); Top 100 searches **100 mi**
  (the site's own "near" radius, `_GEO_NEAR_RADIUS_MI`). If fewer
  pins qualify than requested, the page says so honestly ("Top 73
  near … — that's every eligible haunt within 100 miles").
- **Ordering** — nearest-neighbor from the visitor's point (the tour
  builder's Optimize does the same greedy walk, but from the first
  stop; here we start from *you*), tidied by a bounded 2-opt pass over
  a precomputed haversine matrix (n ≤ 100, fast).
- **Grouping** — the Top 100 master route is chunked into consecutive
  groups of 10, so each night is one geographic leg of the route.
  Displayed per-night mileage is recomputed from home (the visitor
  starts each night at home).
- **Location resolution** (graceful, mirrors the site):
  1. `lat`/`lng` params — browser geolocation ("Use my location"),
     same pattern as `/nearby`;
  2. ZIP — the SMS engine's Census ZCTA centroid table
     (`sms_alerts.zip_centroid`);
  3. town text — the same Nominatim geocoder `/nearby` uses;
  4. Cloudflare visitor geo (Near You's signal) — exact coords when
     the headers carry them, else the resolved area's anchor-town
     centroid, labeled "(approximate center)".
  No center → the page renders the location picker; a wrong area is
  never presented as the visitor's.

## Local verification (Oct 26 production backup DB, Hackensack NJ center)

- Top 10: pool 611 within 50 mi → 10 stops, ~83 mi routed (the
  metro's most-viewed pins genuinely span NJ + NYC + Long Island —
  see the decision below).
- Top 100: pool 1,013 within 100 mi → 100 stops in 10 nights.
  Per-night driving (each night starts from home) runs 26 / 23 / 64 /
  57 / 63 / 37 / 11 / 23 / 58 / **160** mi — the first nine nights are
  comfortable, but the last night sweeps the route's far-edge
  leftovers into one long run. Consecutive chunking is simple and
  predictable; a balanced grouping (spread the far stops across
  nights) is the obvious v2 refinement if Dan wants it.
- End-to-end: night button → POST /api/tours → /t/{slug} renders with
  all stops (verified in the local rig).

## Limits / known gaps

- Distances are straight-line haversine, not road miles (same as the
  rest of the site's distance displays; the /t page's OSRM line and
  Google Maps export give real road routing once opened).
- Category follows the site convention (?cat= works like the
  leaderboards); the homepage buttons use the default halloween map.
- Christmas (Jolly Map) pins enter when `cat=christmas` is passed,
  same as the other Top-N pages.

## Decisions for Dan

1. **Top 10 radius — DECIDED (Dan, Oct 27): 25 mi.** At 50 mi the
   NY-metro Top 10 routed to ~83 mi of driving — a big night. At
   25 mi the pool is still deep (301 near Hackensack) and the night
   is much tighter. Shipped at 25 mi.
2. **Nights of 10** for the Top 100 (could be 8 or 12).
3. Whether auto-tours should also be offered per-category
   (events/stores) later — buttons currently use the default map.
