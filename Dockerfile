FROM python:3.12-slim

WORKDIR /srv

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# ffmpeg for video poster-frame thumbnails
RUN apt-get update && apt-get install -y --no-install-recommends ffmpeg \
    && rm -rf /var/lib/apt/lists/*

COPY . .

# Writable dirs for SQLite + uploads. On hosts with ephemeral disks
# (Render/ Railway free tiers) mount a persistent volume here instead —
# see README "Deploy".
RUN mkdir -p data uploads/thumbs
ENV DATA_DIR=/srv/data UPLOAD_DIR=/srv/uploads

EXPOSE 8000

# Single worker ON PURPOSE (reaffirmed in the Oct 25 blip hardening):
# WAL + busy_timeout made SQLite safe for this process's own threads,
# but the app keeps per-process state — admin sessions, the HTML page
# cache, the analytics writer queue — that a second worker process
# would silently split, and Render runs one instance on one persistent
# disk. The Oct 24 stalls were event-loop blocking (now removed), not
# process count. Revisit only if that state moves out of process.
CMD ["sh", "-c", "uvicorn app.main:app --host 0.0.0.0 --port ${PORT:-8000} --workers 1"]
