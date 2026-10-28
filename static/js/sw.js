/* HauntMap service worker (Wave 1, Oct 27, 2026).
   Two jobs only:
   1) Web Push — show notifications and deep-link clicks into the
      room (payloads are built server-side in app/push.py).
   2) A conservative fetch layer: NETWORK-FIRST for page
      navigations (falling back to a static offline page), and a
      runtime cache for /static/ assets only. API calls and all
      other requests are never intercepted, so this worker can
      never serve a stale or wrong site. */
"use strict";

/* v3 (Oct 28, 2026): bump so installs pick up the self-healing
   offline page (auto-reload on reconnect) — the activate handler
   deletes the older caches, and install re-caches the fresh page.
   OFFLINE_URL carries a ?rev= revision because Cloudflare's edge
   caches /static/ for a month: the bare URL still serves the
   pre-fix page there, while the revisioned URL misses that cache
   and always fetches the current file from origin. Bump BOTH the
   cache name and the rev whenever offline.html changes. */
var STATIC_CACHE = "hauntmap-static-v3";
var OFFLINE_URL = "/static/offline.html?rev=3";

self.addEventListener("install", function (event) {
  event.waitUntil(
    caches.open(STATIC_CACHE)
      .then(function (cache) { return cache.add(OFFLINE_URL); })
      .then(function () { return self.skipWaiting(); })
  );
});

self.addEventListener("activate", function (event) {
  event.waitUntil(
    caches.keys().then(function (names) {
      return Promise.all(names.map(function (name) {
        return name === STATIC_CACHE ? null : caches.delete(name);
      }));
    }).then(function () { return self.clients.claim(); })
  );
});

self.addEventListener("fetch", function (event) {
  var req = event.request;
  if (req.method !== "GET") return;
  var url = new URL(req.url);
  if (url.origin !== self.location.origin) return;

  if (req.mode === "navigate") {
    // Pages: network first, always fresh; offline page only when
    // the network itself is unreachable.
    event.respondWith(
      fetch(req).catch(function () {
        return caches.match(OFFLINE_URL);
      })
    );
    return;
  }

  if (url.pathname.indexOf("/static/") === 0) {
    // Static assets: cache-first with a network fill (they are
    // versioned by query string in the templates).
    event.respondWith(
      caches.match(req).then(function (hit) {
        var fill = fetch(req).then(function (resp) {
          if (resp && resp.status === 200) {
            var copy = resp.clone();
            caches.open(STATIC_CACHE).then(function (cache) {
              cache.put(req, copy);
            });
          }
          return resp;
        }).catch(function () { return hit; });
        return hit || fill;
      })
    );
  }
  // Everything else (API, media, sockets): not intercepted.
});

self.addEventListener("push", function (event) {
  var data = {};
  try { data = event.data ? event.data.json() : {}; } catch (e) { data = {}; }
  var title = data.title || "HauntMap";
  var options = {
    body: data.body || "",
    icon: data.icon || "/static/img/icons/icon-192.png",
    badge: "/static/img/icons/icon-192.png",
    tag: data.tag || "hauntmap",
    data: { url: data.url || "/chat" }
  };
  event.waitUntil(self.registration.showNotification(title, options));
});

self.addEventListener("notificationclick", function (event) {
  event.notification.close();
  var target = (event.notification.data && event.notification.data.url) || "/chat";
  event.waitUntil(
    self.clients.matchAll({ type: "window", includeUncontrolled: true })
      .then(function (windows) {
        for (var i = 0; i < windows.length; i++) {
          var w = windows[i];
          if ("focus" in w) {
            if ("navigate" in w) { w.navigate(target); }
            return w.focus();
          }
        }
        if (self.clients.openWindow) {
          return self.clients.openWindow(target);
        }
      })
  );
});
