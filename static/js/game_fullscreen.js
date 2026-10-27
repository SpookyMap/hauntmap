// Shared game fullscreen toggle (Dan, Oct 27) — every in-site playable
// game gets the same ⛶ affordance: portal_games.js calls
// hmToggleFullscreen(frame) for the GamePix embeds, and Ghost Maze's
// #gm-fs HUD button is wired here to its cabinet (#gm-wrap).
//
// The CONTAINER goes fullscreen (not the bare iframe/canvas), so the
// frame and its controls scale together. Vendor fallbacks included;
// on iPhone Safari, where element fullscreen doesn't exist, the call
// is a guarded no-op — it fails silently rather than throwing, and
// the game keeps playing inline exactly as before.
(function () {
  "use strict";

  function currentFs() {
    return document.fullscreenElement || document.webkitFullscreenElement || null;
  }

  window.hmToggleFullscreen = function (el) {
    if (!el) return;
    try {
      if (currentFs()) {
        var exit = document.exitFullscreen || document.webkitExitFullscreen;
        if (exit) exit.call(document);
        return;
      }
      var req = el.requestFullscreen || el.webkitRequestFullscreen;
      if (!req) return;
      var p = req.call(el);
      if (p && typeof p.catch === "function") p.catch(function () {});
    } catch (e) { /* fullscreen refused — stay inline, never break play */ }
  };

  window.hmExitFullscreenIf = function (el) {
    try {
      if (el && currentFs() === el) {
        var exit = document.exitFullscreen || document.webkitExitFullscreen;
        if (exit) exit.call(document);
      }
    } catch (e) { /* no-op */ }
  };

  // Ghost Maze cabinet button (ghost_maze.html renders #gm-fs in the HUD).
  var gmBtn = document.getElementById("gm-fs");
  if (gmBtn) {
    gmBtn.addEventListener("click", function () {
      window.hmToggleFullscreen(document.getElementById("gm-wrap"));
    });
  }
})();
