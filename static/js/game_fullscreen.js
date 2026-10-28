// Shared game fullscreen toggle (Dan, Oct 27) — every in-site playable
// game gets the same ⛶ affordance: portal_games.js calls
// hmToggleFullscreen(frame) for the GamePix embeds, and Ghost Maze's
// #gm-fs HUD button is wired here to its cabinet (#gm-wrap).
//
// The CONTAINER goes fullscreen (not the bare iframe/canvas), so the
// frame and its controls scale together. Native Fullscreen API is used
// wherever it actually works (desktop, Android, iPad). iPhone Safari
// has NO element fullscreen for non-video elements — requestFullscreen
// simply doesn't exist there — so the first build silently no-opped on
// iPhones and the ⛶ button looked dead (Dan's report, Oct 27 night).
//
// Fix (same night): when the native API is missing, rejects, or errors,
// fall back to a CSS pseudo-fullscreen: the container goes
// position:fixed over the whole viewport (100dvw x 100dvh, so rotation
// and Safari's collapsing chrome are handled by the units), the page
// behind it is scroll-locked, and the same ⛶ / ✕ controls exit it —
// restoring the exact prior layout and scroll position. Safari's own
// browser chrome (URL bar etc.) can still show over a web page; that's
// Apple's limit, not something page code can override.
(function () {
  "use strict";

  var pseudoEl = null;   // element currently in CSS pseudo-fullscreen
  var pendingEl = null;  // element with a native request in flight
  var saved = null;      // scroll/body snapshot for exact restore

  // Pseudo-fullscreen styles travel with this file (injected once) so
  // the fix ships without stylesheet-token churn. dvh/dvw cascade over
  // vh/vw for engines too old to know them.
  var style = document.createElement("style");
  style.id = "hm-pseudo-fs-css";
  style.textContent =
    ".hm-pseudo-fs{position:fixed!important;inset:0!important;" +
    "width:100vw!important;width:100dvw!important;" +
    "height:100vh!important;height:100dvh!important;" +
    "max-width:none!important;max-height:none!important;" +
    "margin:0!important;aspect-ratio:auto!important;" +
    "border:0!important;border-radius:0!important;" +
    "z-index:100000!important;background:#000;}" +
    ".hm-pseudo-fs iframe{width:100%!important;height:100%!important;}" +
    "html.hm-fs-lock,body.hm-fs-lock{overflow:hidden!important;}" +
    // Ghost Maze cabinet: mirror its :fullscreen layout in pseudo mode.
    ".gm-wrap.hm-pseudo-fs{display:flex;flex-direction:column;" +
    "align-items:center;justify-content:center;padding:.5rem;" +
    "box-sizing:border-box;overflow:auto;background:#05080a;}" +
    ".gm-wrap.hm-pseudo-fs .gm-hud,.gm-wrap.hm-pseudo-fs .gm-stage{" +
    "width:min(96vw,calc((100vh - 200px)*0.7917));" +
    "width:min(96vw,calc((100dvh - 200px)*0.7917));flex:none;}";
  (document.head || document.documentElement).appendChild(style);

  function currentFs() {
    return document.fullscreenElement || document.webkitFullscreenElement || null;
  }

  function lockScroll() {
    var y = window.scrollY || window.pageYOffset || 0;
    var b = document.body;
    saved = {
      y: y,
      position: b.style.position, top: b.style.top, left: b.style.left,
      right: b.style.right, width: b.style.width
    };
    document.documentElement.classList.add("hm-fs-lock");
    b.classList.add("hm-fs-lock");
    // overflow:hidden alone doesn't stop iOS rubber-band scrolling;
    // pinning the body does. Everything it shifts sits behind the
    // overlay for the duration, and unlockScroll restores it exactly.
    b.style.position = "fixed";
    b.style.top = (-y) + "px";
    b.style.left = "0";
    b.style.right = "0";
    b.style.width = "100%";
  }

  function unlockScroll() {
    if (!saved) return;
    var b = document.body;
    document.documentElement.classList.remove("hm-fs-lock");
    b.classList.remove("hm-fs-lock");
    b.style.position = saved.position;
    b.style.top = saved.top;
    b.style.left = saved.left;
    b.style.right = saved.right;
    b.style.width = saved.width;
    window.scrollTo(0, saved.y);
    saved = null;
  }

  function enterPseudo(el) {
    if (pseudoEl || currentFs()) return;
    lockScroll();
    pseudoEl = el;
    el.classList.add("hm-pseudo-fs");
  }

  function exitPseudo() {
    if (!pseudoEl) return;
    pseudoEl.classList.remove("hm-pseudo-fs");
    pseudoEl = null;
    unlockScroll();
  }

  function exitNative() {
    var exit = document.exitFullscreen || document.webkitExitFullscreen;
    if (exit) exit.call(document);
  }

  window.hmToggleFullscreen = function (el) {
    if (!el) return;
    // Already in pseudo-fullscreen: the same ⛶ toggles back out.
    if (pseudoEl) { exitPseudo(); return; }
    try {
      if (currentFs()) { exitNative(); return; }
      var req = el.requestFullscreen || el.webkitRequestFullscreen;
      if (!req) { enterPseudo(el); return; }  // iPhone Safari lands here
      pendingEl = el;
      var p = req.call(el);
      if (p && typeof p.catch === "function") {
        p.catch(function () {
          if (pendingEl === el) { pendingEl = null; enterPseudo(el); }
        });
      }
      // Engines too old to return a promise report failure only via
      // the fullscreenerror event — handled below.
    } catch (e) {
      pendingEl = null;
      enterPseudo(el);
    }
  };

  window.hmExitFullscreenIf = function (el) {
    try {
      if (el && pseudoEl === el) { exitPseudo(); return; }
      if (el && currentFs() === el) exitNative();
    } catch (e) { /* no-op */ }
  };

  function onFsError() {
    if (pendingEl) { var el = pendingEl; pendingEl = null; enterPseudo(el); }
  }
  document.addEventListener("fullscreenerror", onFsError);
  document.addEventListener("webkitfullscreenerror", onFsError);
  document.addEventListener("fullscreenchange", function () {
    if (currentFs()) pendingEl = null;
  });
  document.addEventListener("webkitfullscreenchange", function () {
    if (currentFs()) pendingEl = null;
  });
  document.addEventListener("keydown", function (e) {
    if (pseudoEl && (e.key === "Escape" || e.key === "Esc")) exitPseudo();
  });

  // Ghost Maze cabinet button (ghost_maze.html renders #gm-fs in the HUD).
  var gmBtn = document.getElementById("gm-fs");
  if (gmBtn) {
    gmBtn.addEventListener("click", function () {
      window.hmToggleFullscreen(document.getElementById("gm-wrap"));
    });
  }
})();
