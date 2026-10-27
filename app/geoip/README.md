# Bundled IP geolocation database

`GeoLite2-City.mmdb` is the **GeoLite2 City** database created by
**MaxMind** (https://www.maxmind.com), free edition, build of
2026-10-21, obtained via the P3TERX/GeoLite.mmdb mirror release
`2026.10.25`.

It is used by exactly one thing: the analytics writer thread in
`app/main.py` resolves a page view's stored visitor IP address to a
U.S. state when Cloudflare's location headers didn't carry one, so
the /admin/stats "U.S. states" table can say which states are
visiting. Internal analytics only; the address itself is never
displayed, no data leaves the server, and no per-request external
API calls are made.

To refresh: download a newer GeoLite2-City.mmdb and replace the file
(same name), then redeploy. If the file is missing, state resolution
silently falls back to Cloudflare headers only.
