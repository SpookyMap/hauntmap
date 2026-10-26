// Portal catalog click-to-load (Dan, Oct 26) — the /games hub renders
// lightweight facades (cover art + Play) for GamePix partner games;
// the real iframe is only created when a visitor taps Play, so the
// hub stays fast and the fortify render budget never feels them.
// One game plays at a time: opening another closes the first, and
// the ✕ on a running game tears its iframe down (stops its audio/CPU)
// and restores the facade.
//
// Oct 26 swap: GameDistribution rejected HauntMap's publisher
// registration on traffic grounds and its embeds render a
// "NOT AVAILABLE HERE" interstitial on gethauntmap.com, so the
// arcade moved to GamePix's open webmaster embed program — games are
// embedded via play.gamepix.com/<slug>/embed, no domain approval.
// SID below is the publisher id GamePix distributes in its public
// demo feed; swap in HauntMap's own free GamePix sid here if Dan
// ever wants the plays attributed to HauntMap.
(function () {
  "use strict";
  var SID = "62R39";

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
    var slug = card.getAttribute("data-game-slug");
    if (!frame || !slug) return;
    var iframe = document.createElement("iframe");
    iframe.src = "https://play.gamepix.com/" + slug + "/embed?sid=" + SID;
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
