/* Haunt Chat Wave 1 — web push opt-in (Oct 27, 2026).
   Drives the shared _push_settings.html panel (chat page + profile
   edit). Rules of the road:
   - The browser permission prompt fires ONLY from the member's own
     tap on the master switch — never on page load.
   - The master switch subscribes THIS device; the per-type switches
     are server-side preferences and save immediately.
   - iOS only delivers push to the INSTALLED PWA, so on iPhone/iPad
     outside standalone mode we explain Add to Home Screen instead
     of pretending to subscribe. */
(function () {
  "use strict";
  var panel = document.querySelector("[data-push-panel]");
  if (!panel) return;

  var master = panel.querySelector("[data-push-master]");
  var kindBoxes = panel.querySelectorAll("[data-push-kind]");
  var statusEl = panel.querySelector("[data-push-status]");
  var iosEl = panel.querySelector("[data-push-ios]");
  var msgEl = panel.querySelector("[data-push-msg]");
  var testBtn = panel.querySelector("[data-push-test]");

  var cfg = { configured: false, public_key: null };
  var settings = null;

  function api(path, body) {
    var opts = { credentials: "same-origin",
                 headers: { "Content-Type": "application/json" } };
    if (body !== undefined) {
      opts.method = "POST";
      opts.body = JSON.stringify(body);
    }
    return fetch(path, opts).then(function (r) { return r.json(); });
  }

  function say(text) { if (msgEl) msgEl.textContent = text; }

  function isIOS() {
    return /iphone|ipad|ipod/i.test(navigator.userAgent) ||
      (navigator.platform === "MacIntel" && navigator.maxTouchPoints > 1);
  }

  function isStandalone() {
    return (window.matchMedia &&
            window.matchMedia("(display-mode: standalone)").matches) ||
      window.navigator.standalone === true;
  }

  function pushSupported() {
    return "serviceWorker" in navigator && "PushManager" in window &&
      "Notification" in window;
  }

  function urlB64ToUint8Array(b64) {
    var padding = "=".repeat((4 - (b64.length % 4)) % 4);
    var base64 = (b64 + padding).replace(/-/g, "+").replace(/_/g, "/");
    var raw = window.atob(base64);
    var out = new Uint8Array(raw.length);
    for (var i = 0; i < raw.length; i++) out[i] = raw.charCodeAt(i);
    return out;
  }

  function render() {
    if (!settings) return;
    master.checked = !!settings.enabled;
    kindBoxes.forEach(function (box) {
      box.checked = !!settings[box.getAttribute("data-push-kind")];
      box.disabled = !settings.enabled;
    });
    if (testBtn) testBtn.disabled = !settings.enabled;
    var notes = [];
    if (!cfg.configured) {
      notes.push("Notifications aren't switched on for HauntMap " +
                 "yet — this panel will come alive when they are.");
    } else if (!pushSupported()) {
      if (isIOS() && !isStandalone()) {
        if (iosEl) iosEl.hidden = false;
      } else {
        notes.push("This browser doesn't support push " +
                   "notifications.");
      }
    } else if (window.Notification &&
               Notification.permission === "denied") {
      notes.push("Notifications are blocked for HauntMap in your " +
                 "browser settings — allow them there, then flip " +
                 "the switch again.");
    } else if (settings.enabled) {
      notes.push("On 🎃 — we'll only message this device about " +
                 "the kinds ticked below.");
    } else {
      notes.push("Off. Flip the switch and we'll ask your browser " +
                 "for permission — nothing is sent until you say yes.");
    }
    if (statusEl) statusEl.textContent = notes.join(" ");
  }

  function saveSettings(patch) {
    var merged = Object.assign({}, settings, patch);
    return api("/api/push/settings", merged).then(function (res) {
      if (res && res.settings) settings = res.settings;
      render();
      return res;
    });
  }

  function subscribeDevice() {
    return navigator.serviceWorker.ready.then(function (reg) {
      return reg.pushManager.getSubscription().then(function (sub) {
        if (sub) return sub;
        return reg.pushManager.subscribe({
          userVisibleOnly: true,
          applicationServerKey: urlB64ToUint8Array(cfg.public_key)
        });
      });
    }).then(function (sub) {
      return api("/api/push/subscribe", sub.toJSON());
    });
  }

  function unsubscribeDevice() {
    if (!("serviceWorker" in navigator)) return Promise.resolve();
    return navigator.serviceWorker.ready.then(function (reg) {
      return reg.pushManager.getSubscription();
    }).then(function (sub) {
      if (!sub) return null;
      var endpoint = sub.endpoint;
      return api("/api/push/unsubscribe", { endpoint: endpoint })
        .then(function () { return sub.unsubscribe(); });
    }).catch(function () { /* best effort */ });
  }

  master.addEventListener("change", function () {
    if (master.checked) {
      if (!cfg.configured) {
        master.checked = false;
        say("Notifications aren't switched on for the site yet.");
        return;
      }
      if (!pushSupported()) {
        master.checked = false;
        if (isIOS() && !isStandalone() && iosEl) {
          iosEl.hidden = false;
          say("One quick install step first — see the note above. 🍎");
        } else {
          say("This browser doesn't support push notifications.");
        }
        return;
      }
      say("Asking your browser…");
      Notification.requestPermission().then(function (perm) {
        if (perm !== "granted") {
          master.checked = false;
          say("No problem — permission wasn't granted, so " +
              "nothing was turned on.");
          render();
          return null;
        }
        return subscribeDevice().then(function () {
          return saveSettings({ enabled: 1 });
        }).then(function () {
          say("You're in! 🎃 Try the test button below.");
        });
      }).catch(function () {
        master.checked = false;
        say("Something went wrong subscribing this device.");
        render();
      });
    } else {
      unsubscribeDevice().then(function () {
        return saveSettings({ enabled: 0 });
      }).then(function () {
        say("Off — this device won't hear from the room.");
      });
    }
  });

  kindBoxes.forEach(function (box) {
    box.addEventListener("change", function () {
      var patch = {};
      patch[box.getAttribute("data-push-kind")] = box.checked ? 1 : 0;
      saveSettings(patch).then(function () { say("Saved."); });
    });
  });

  if (testBtn) {
    testBtn.addEventListener("click", function () {
      say("Sending…");
      api("/api/push/test", {}).then(function (res) {
        say(res && res.ok ? "Test sent — check your notifications! 🎃"
                          : ((res && res.error) || "Test failed."));
      }).catch(function () { say("Test failed."); });
    });
  }

  // Panel open/close (chat page bell button).
  document.querySelectorAll("[data-push-open]").forEach(function (btn) {
    btn.addEventListener("click", function () {
      var target = document.getElementById(
        btn.getAttribute("data-push-open"));
      if (target) target.hidden = !target.hidden;
    });
  });
  var closeBtn = panel.querySelector("[data-push-close]");
  if (closeBtn) {
    closeBtn.addEventListener("click", function () {
      var wrap = panel.closest("[data-push-wrap]");
      if (wrap) wrap.hidden = true;
    });
  }

  Promise.all([api("/api/push/config"), api("/api/push/settings")])
    .then(function (results) {
      cfg = results[0] || cfg;
      if (results[1] && results[1].settings) {
        settings = results[1].settings;
        render();
      } else {
        // Guest view (shouldn't happen — the panel is member-only):
        // hide the whole surface quietly.
        var wrap = panel.closest("[data-push-wrap]") || panel;
        wrap.style.display = "none";
      }
    })
    .catch(function () { /* panel stays inert */ });
})();
