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

# Single worker: SQLite does not like concurrent writers.
CMD ["sh", "-c", "uvicorn app.main:app --host 0.0.0.0 --port ${PORT:-8000} --workers 1"]
