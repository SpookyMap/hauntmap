// =====================================================================
// Retention Wave 2 — Items 3 + 5 (branch retention2-capture).
// Loaded once from base.html (defer) alongside templates/_capture_prompt.html.
//
// ITEM 5 — Daily Fright streak state, ONE source of truth:
//   The streak itself is counted ONLY by hmFrightTouch() in base.html
//   (cookies hm_fright_streak / hm_fright_last / hm_fright_freeze; the
//   day boundary is hmFrightTodayET() = the America/New_York calendar
//   date, i.e. the drop flips at ET midnight — the same boundary
//   /daily, the homepage band and _today_et() server-side all use).
//   NOTE: the wave brief said "localStorage", but the shipped streak
//   is cookie-based; this file deliberately reuses the shipped store.
//   hmFrightState() below is a READ-ONLY projection of that state for
//   display (the pin-page chip). It never writes the cookies, never
//   counts a day and never consumes a freeze — pin pages are NOT a
//   counting surface, so merely viewing pins cannot build a streak.
//   /daily and the homepage band keep calling hmFrightTouch() exactly
//   as before; both paths derive from the same cookies + the same
//   hmFrightTodayET() helper, so there is still one source of truth.
//
// ITEM 3 — Mid-browse text-alert capture sheet (#hm-capture):
//   localStorage keys (all prefixed hm_ta_):
//     hm_ta_plays      int, video plays counted ACROSS pages (one
//                      counter, never forked per page)
//     hm_ta_prompt_at  ms timestamp of the last time the sheet was
//                      shown (set at show time, so dismissing or
//                      ignoring both start the ~3-day window)
//     hm_ta_subscribed '1' once this visitor has signed up for text
//                      alerts through ANY surface (see below)
//   Triggers (first one wins): the visitor's 2nd counted video play,
//   or ~25s of tab-visible time on the page.
//   Suppression: already subscribed; homepage (the static panel lives
//   there); any page that already renders a static .text-alerts panel
//   (/events, /virtual-tour — no duplicate forms); /admin; shown
//   within the last ~3 days. PIN PAGES (/d/{id}) are EXEMPT from the
//   static-panel suppression (Dan, 2026-10-23): most traffic lands
//   there, so the sheet fires on pin pages too, panel notwithstanding.
//   Subscribed detection: POST /text-alerts is a classic form POST
//   that 303-redirects back with ?text_alerts=1|code|confirmed in the
//   URL, so any landing page carrying that flag marks the visitor
//   subscribed here. The sheet's own submit does the same on success.
// =====================================================================
(function () {
  'use strict';

  function lsGet(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }
  function lsSet(k, v) { try { localStorage.setItem(k, v); } catch (e) {} }

  // ---------------- Item 5: streak state + pin-page chip -------------
  function hmFrightState() {
    var getCookie = (typeof window.hmFrightGetCookie === 'function')
      ? window.hmFrightGetCookie
      : function (name) {
          var m = document.cookie.match(new RegExp('(?:^|; )' + name + '=([^;]*)'));
          return m ? decodeURIComponent(m[1]) : '';
        };
    var today = (typeof window.hmFrightTodayET === 'function')
      ? window.hmFrightTodayET()
      : new Date().toISOString().slice(0, 10);
    var streak = parseInt(getCookie('hm_fright_streak') || '0', 10) || 0;
    var last = getCookie('hm_fright_last');
    var done = last === today;
    return {
      today: today,
      last: last,
      streak: streak,
      doneToday: done,
      // The stored streak is only "live" once today has been counted
      // by a counting surface; an uncounted today means the chip
      // invites, it does not quote a number.
      liveStreak: done ? Math.max(streak, 1) : 0
    };
  }
  window.hmFrightState = hmFrightState;

  document.querySelectorAll('[data-fright-chip]').forEach(function (el) {
    var s = hmFrightState();
    if (s.doneToday) {
      // Day-boundary copy matches the shipped drop: the next fright
      // lands at midnight Eastern (hmFrightTodayET / _today_et).
      el.textContent = '\u{1F525} Day ' + s.liveStreak +
        ' \u2014 tomorrow\u2019s fright unlocks at midnight ET';
    } else {
      el.textContent = '\u{1F525} Today\u2019s fright is waiting \u2192';
    }
    el.hidden = false;
  });

  // ---------------- Item 3: capture sheet ----------------------------
  var THREE_DAYS_MS = 3 * 24 * 3600 * 1000;
  var ENGAGED_SECONDS = 25;
  var sheet = document.getElementById('hm-capture');
  if (!sheet) return;

  // Mark subscribed when a panel/sheet signup lands back on any page.
  try {
    if (/[?&]text_alerts=(1|code|confirmed)(&|$)/.test(location.search)) {
      lsSet('hm_ta_subscribed', '1');
    }
  } catch (e) {}

  var shown = false;

  function displayEligible() {
    if (lsGet('hm_ta_subscribed') === '1') return false;
    var path = location.pathname;
    if (path === '/' || path.indexOf('/admin') === 0) return false;
    var last = parseInt(lsGet('hm_ta_prompt_at') || '0', 10) || 0;
    if (last && (Date.now() - last) < THREE_DAYS_MS) return false;
    // No duplication: pages with a static text-alerts panel already
    // carry the form (/events, /virtual-tour) — EXCEPT pin pages.
    // Dan 2026-10-23: pin pages are where most traffic lands, so the
    // sheet fires there too despite the static panel.
    var onPinPage = /^\/d\/\d+/.test(path);
    if (!onPinPage && document.querySelector('.text-alerts')) return false;
    return true;
  }

  function prefill() {
    var town = lsGet('hm_town') || '';
    var townInput = sheet.querySelector('input[name="town"]');
    var zipInput = sheet.querySelector('input[name="zip"]');
    if (townInput && town && !townInput.value) townInput.value = town;
    var zip = (town.match(/\b\d{5}\b/) || [])[0];
    if (zipInput && zip && !zipInput.value) zipInput.value = zip;
  }

  function showSheet() {
    if (shown || !displayEligible()) return;
    shown = true;
    lsSet('hm_ta_prompt_at', String(Date.now()));
    prefill();
    sheet.hidden = false;
    // Next frame so the slide-in transition runs from the off state.
    requestAnimationFrame(function () {
      requestAnimationFrame(function () { sheet.classList.add('hm-capture-in'); });
    });
  }

  function hideSheet() {
    sheet.classList.remove('hm-capture-in');
    setTimeout(function () { sheet.hidden = true; }, 350);
  }

  var xBtn = sheet.querySelector('.hm-capture-x');
  if (xBtn) xBtn.addEventListener('click', hideSheet);
  document.addEventListener('keydown', function (ev) {
    if (ev.key === 'Escape' && shown && !sheet.hidden) hideSheet();
  });

  // --- Trigger A: video plays, one counter across pages ---------------
  // Play signals, all delegated so no per-page/per-template forks:
  //   .tt-facade click/keydown  -> hmLoadTikTok() in base.html (the
  //     facade's own handlers run first; the event still bubbles to
  //     document with the facade as target even though the node has
  //     been replaced by the embed by then)
  //   .yt-facade click          -> the YouTube facade buttons on
  //     /music, /movies, /diy-costumes (same delegation shape)
  //   native <video> 'play'     -> capture phase (media events do
  //     not bubble); counted once per element via dataset flag.
  function countPlay(el) {
    if (!el || el.dataset.hmTaCounted) return;
    el.dataset.hmTaCounted = '1';
    var n = (parseInt(lsGet('hm_ta_plays') || '0', 10) || 0) + 1;
    lsSet('hm_ta_plays', String(n));
    if (n >= 2) showSheet();
  }
  document.addEventListener('click', function (ev) {
    var f = ev.target && ev.target.closest && ev.target.closest('.tt-facade, .yt-facade');
    if (f) countPlay(f);
  });
  document.addEventListener('keydown', function (ev) {
    if (ev.key !== 'Enter' && ev.key !== ' ') return;
    var f = ev.target && ev.target.closest && ev.target.closest('.tt-facade');
    if (f) countPlay(f);
  });
  document.addEventListener('play', function (ev) {
    if (ev.target && ev.target.tagName === 'VIDEO') countPlay(ev.target);
  }, true);
  // Arriving with 2+ plays already banked (e.g. counted on the
  // homepage, where the sheet never displays) still needs a trigger
  // on this page: the engaged timer below is that trigger.

  // --- Trigger B: ~25s of engaged (tab-visible) time on the page ----
  var engaged = 0;
  var timer = setInterval(function () {
    if (shown) { clearInterval(timer); return; }
    if (document.visibilityState !== 'visible') return;
    engaged += 1;
    if (engaged >= ENGAGED_SECONDS) {
      clearInterval(timer);
      showSheet();
    }
  }, 1000);

  // --- Submit: same POST /text-alerts contract as the static panel ---
  var form = sheet.querySelector('.hm-capture-form');
  var errorEl = sheet.querySelector('.hm-capture-error');
  var doneEl = sheet.querySelector('.hm-capture-done');
  var SMS_ERRORS = {
    phone: 'Please enter a valid 10-digit US mobile number.',
    zip: 'Add your ZIP code so we know how far to look around you.',
    town: 'For town-only alerts, add your town (e.g. Morristown, NJ).'
  };
  if (form) {
    form.addEventListener('submit', function (ev) {
      ev.preventDefault();
      if (!window.fetch || !window.FormData) { form.submit(); return; }
      var btn = form.querySelector('button[type="submit"]');
      if (btn) btn.disabled = true;
      if (errorEl) errorEl.hidden = true;
      fetch('/text-alerts', {
        method: 'POST',
        body: new FormData(form),
        credentials: 'same-origin'
      }).then(function (r) {
        // The endpoint 303-redirects back to the referer with flags;
        // fetch follows it, so the final URL carries the outcome —
        // exactly the state the static panel renders from.
        var q = (r.url || '').split('?')[1] || '';
        var params = new URLSearchParams(q);
        var err = params.get('sms_error');
        if (err) {
          if (errorEl) {
            errorEl.textContent = SMS_ERRORS[err] || 'That didn\u2019t go through \u2014 check the form and try again.';
            errorEl.hidden = false;
          }
          if (btn) btn.disabled = false;
          return;
        }
        var state = params.get('text_alerts');
        if (state === '1' || state === 'code' || state === 'confirmed') {
          lsSet('hm_ta_subscribed', '1');
          form.hidden = true;
          var consent = sheet.querySelector('.ta-consent');
          if (consent) consent.hidden = true;
          if (doneEl) {
            doneEl.textContent = state === 'code'
              ? '\u{1F4F1} Almost there \u2014 we just texted you a 6-digit code. Enter it in the text-alerts panel to turn your alerts on.'
              : '\u{1F389} You\u2019re on the list \u2014 we\u2019ll text a confirmation when alerts launch.';
            doneEl.hidden = false;
          }
          setTimeout(hideSheet, 4200);
          return;
        }
        if (btn) btn.disabled = false;
      }).catch(function () {
        // Network failure: fall back to the classic full-page POST,
        // which behaves exactly like the static panel.
        form.submit();
      });
    });
  }
})();
