#!/usr/bin/env python3
"""Build app/geo/us-counties.json from the Census county GeoJSON
(plotly/datasets geojson-counties-fips.json, TIGER-derived).

Output is a compact bundle the quest engine loads server-side for
point-in-polygon county resolution: one record per county with its
FIPS, display name, state USPS code, bounding box, and polygon rings
(coordinates rounded to 4 decimals, ~11 m — plenty for "which county
is this display in"). Rings layout: polys = [polygon, ...], polygon
= [ring, ...] (outer ring first, then holes), ring = [[lng, lat]...].

Usage: python3 scripts/build_counties_geo.py <raw-geojson> \
           [out=app/geo/us-counties.json]
"""
import json
import sys
from pathlib import Path

STATE_FIPS = {
    "01": "AL", "02": "AK", "04": "AZ", "05": "AR", "06": "CA",
    "08": "CO", "09": "CT", "10": "DE", "11": "DC", "12": "FL",
    "13": "GA", "15": "HI", "16": "ID", "17": "IL", "18": "IN",
    "19": "IA", "20": "KS", "21": "KY", "22": "LA", "23": "ME",
    "24": "MD", "25": "MA", "26": "MI", "27": "MN", "28": "MS",
    "29": "MO", "30": "MT", "31": "NE", "32": "NV", "33": "NH",
    "34": "NJ", "35": "NM", "36": "NY", "37": "NC", "38": "ND",
    "39": "OH", "40": "OK", "41": "OR", "42": "PA", "44": "RI",
    "45": "SC", "46": "SD", "47": "TN", "48": "TX", "49": "UT",
    "50": "VT", "51": "VA", "53": "WA", "54": "WV", "55": "WI",
    "56": "WY", "72": "PR", "66": "GU", "78": "VI", "60": "AS",
    "69": "MP",
}


def _ring(ring):
    return [[round(x, 4), round(y, 4)] for x, y in ring]


def main() -> None:
    src = Path(sys.argv[1])
    out = Path(sys.argv[2]) if len(sys.argv) > 2 else \
        Path(__file__).parent.parent / "app" / "geo" / "us-counties.json"
    data = json.loads(src.read_text())
    counties = []
    for feat in data["features"]:
        props = feat["properties"]
        fips = props["GEO_ID"][-5:]
        geom = feat["geometry"]
        if geom["type"] == "Polygon":
            polys = [[_ring(r) for r in geom["coordinates"]]]
        elif geom["type"] == "MultiPolygon":
            polys = [[_ring(r) for r in poly]
                     for poly in geom["coordinates"]]
        else:
            continue
        xs = [p[0] for poly in polys for ring in poly for p in ring]
        ys = [p[1] for poly in polys for ring in poly for p in ring]
        lsad = (props.get("LSAD") or "County").strip()
        name = props["NAME"] if lsad == "" else \
            f"{props['NAME']} {lsad}"
        counties.append({
            "fips": fips,
            "name": name,
            "state": STATE_FIPS.get(props["STATE"], ""),
            "bbox": [round(min(xs), 4), round(min(ys), 4),
                     round(max(xs), 4), round(max(ys), 4)],
            "polys": polys,
        })
    counties.sort(key=lambda c: c["fips"])
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"counties": counties},
                              separators=(",", ":")))
    print(f"wrote {len(counties)} counties to {out} "
          f"({out.stat().st_size / 1e6:.2f} MB)")


if __name__ == "__main__":
    main()
