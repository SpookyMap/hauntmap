// Portal catalog click-to-load (Dan, Oct 26) — the /games hub renders
// lightweight facades (cover art + Play) for GameDistribution partner
// games; the real iframe is only created when a visitor taps Play, so
// the hub stays fast and the fortify render budget never feels them.
// One game plays at a time: opening another closes the first, and the
// ✕ on a running game tears its iframe down (stops its audio/CPU) and
// restores the facade.
(function () {
  "use strict";
  var REFERRER = "https://gethauntmap.com/games";

  function resetCard(card) {
    var frame = card.querySelector(".portal-frame");
    if (!frame) return;
    frame.innerHTML = card._facadeHTML;
    card.classList.remove("is-playing");
    wireFacade(card);
  }

  function playCard(card) {
    document.querySelectorAll(".portal-card.is-playing").forEach(function (other) {
      if (other !== card) resetCard(other);
    });
    var frame = card.querySelector(".portal-frame");
    var id = card.getAttribute("data-game-id");
    if (!frame || !id) return;
    var iframe = document.createElement("iframe");
    iframe.src = "https://html5.gamedistribution.com/" + id +
      "/?gd_sdk_referrer_url=" + encodeURIComponent(REFERRER);
    iframe.title = card.getAttribute("data-game-title") || "Game";
    iframe.setAttribute("frameborder", "0");
    iframe.setAttribute("scrolling", "no");
    iframe.setAttribute("allowfullscreen", "");
    iframe.setAttribute("allow", "autoplay; fullscreen");
    var close = document.createElement("button");
    close.type = "button";
    close.className = "portal-close";
    close.setAttribute("aria-label", "Close game");
    close.textContent = "\u2715";
    close.addEventListener("click", function () { resetCard(card); });
    frame.innerHTML = "";
    frame.appendChild(iframe);
    frame.appendChild(close);
    card.classList.add("is-playing");
    card.scrollIntoView({ block: "nearest", behavior: "smooth" });
  }

  function wireFacade(card) {
    var btn = card.querySelector(".portal-facade");
    if (btn) btn.addEventListener("click", function () { playCard(card); });
  }

  document.querySelectorAll(".portal-card").forEach(function (card) {
    var frame = card.querySelector(".portal-frame");
    if (frame) card._facadeHTML = frame.innerHTML;
    wireFacade(card);
  });
})();
