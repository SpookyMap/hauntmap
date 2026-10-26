/* GHOST MAZE — HauntMap's own maze-chase arcade game.
   Everything on the board is original to HauntMap and drawn or
   synthesized in code: the maze layout, the ghost with his map-pin
   eyes, Frank and the monster crew, and every bleep (WebAudio).
   The genre's mechanics — munch, chase, frighten, chain — are just
   rules; rules belong to everyone. No third-party assets. */
(function () {
  "use strict";

  // ---------------------------------------------------------- maze
  // 19 x 24, drawn for HauntMap: a haunted-neighborhood grid with a
  // monster house in the middle and one wrap-around tunnel street.
  // # wall · . candy · o power pumpkin · = house door · H house
  var MAZE = [
    "###################",
    "#........#........#",
    "#.##.##..#..##.##.#",
    "#o##.##.....##.##o#",
    "#.................#",
    "#.##.#.#####.#.##.#",
    "#....#...#...#....#",
    "####.###.#.###.####",
    "####.#.......#.####",
    "####.#.##=##.#.####",
    "####.#.#HHH#.#.####",
    "####.#.#####.#.####",
    "...................",
    "####.#.#####.#.####",
    "####.#.......#.####",
    "####.#.#####.#.####",
    "#........#........#",
    "#.##.##..#..##.##.#",
    "#o.#.....P.....#.o#",
    "##.#.#.#####.#.####",
    "#....#...#...#....#",
    "#.######.#.######.#",
    "#.................#",
    "###################"
  ];
  var COLS = 19, ROWS = 24, TILE = 22;
  var TUNNEL_ROW = 12;
  var DOOR = { x: 9, y: 9 }, DOOR_FRONT = { x: 9, y: 8 };
  var PEN = { x: 9, y: 10 };
  var BUCKET_TILE = { x: 9, y: 14 };
  var PLAYER_SPAWN = { x: 9, y: 18 };

  var grid = MAZE.map(function (r) { return r.split(""); });
  function cellAt(x, y) {
    if (y === TUNNEL_ROW && (x < 0 || x >= COLS)) return ".";
    if (x < 0 || x >= COLS || y < 0 || y >= ROWS) return "#";
    return grid[y][x];
  }
  // who: "player" | "chaser" — house tiles and the door are
  // chaser-only, and only while leaving / entering / eyes-returning.
  function canPass(x, y, who, mode) {
    if (y === TUNNEL_ROW && (x < 0 || x >= COLS)) return true;
    var c = cellAt(x, y);
    if (c === "#") return false;
    if (c === "=") return who === "chaser" &&
      (mode === "leaving" || mode === "entering");
    if (c === "H") return who === "chaser" &&
      (mode === "leaving" || mode === "entering" || mode === "inpen");
    return true;
  }
  // BFS distances to the house door-front, for returning eyes.
  var doorDist = (function () {
    var dist = {}, q = [[DOOR_FRONT.x, DOOR_FRONT.y]];
    dist[DOOR_FRONT.x + "," + DOOR_FRONT.y] = 0;
    while (q.length) {
      var cur = q.shift(), cx = cur[0], cy = cur[1];
      [[1, 0], [-1, 0], [0, 1], [0, -1]].forEach(function (d) {
        var nx = cx + d[0], ny = cy + d[1];
        if (ny === TUNNEL_ROW) nx = ((nx % COLS) + COLS) % COLS; // wrap
        var k = nx + "," + ny;
        if (dist[k] !== undefined) return;
        var c = cellAt(nx, ny);
        if (c === "#" || c === "H" || c === "=") return;
        dist[k] = dist[cx + "," + cy] + 1;
        q.push([nx, ny]);
      });
    }
    return dist;
  })();

  var DIRS = {
    up: { x: 0, y: -1 }, down: { x: 0, y: 1 },
    left: { x: -1, y: 0 }, right: { x: 1, y: 0 }
  };
  function rev(d) { return { x: -d.x, y: -d.y }; }
  function sameDir(a, b) { return a.x === b.x && a.y === b.y; }

  // ---------------------------------------------------------- audio
  // Original bleeps, synthesized. No samples, no borrowed tunes.
  var AudioSys = {
    ctx: null, muted: localStorage.getItem("gm_muted") === "1",
    ensure: function () {
      if (!this.ctx) {
        try { this.ctx = new (window.AudioContext ||
          window.webkitAudioContext)(); } catch (e) { this.ctx = null; }
      }
      if (this.ctx && this.ctx.state === "suspended") this.ctx.resume();
    },
    tone: function (f0, f1, dur, type, vol, delay) {
      if (!this.ctx || this.muted) return;
      var t = this.ctx.currentTime + (delay || 0);
      var o = this.ctx.createOscillator(), g = this.ctx.createGain();
      o.type = type || "square";
      o.frequency.setValueAtTime(f0, t);
      if (f1 && f1 !== f0)
        o.frequency.exponentialRampToValueAtTime(Math.max(f1, 1), t + dur);
      g.gain.setValueAtTime(vol || 0.08, t);
      g.gain.exponentialRampToValueAtTime(0.001, t + dur);
      o.connect(g); g.connect(this.ctx.destination);
      o.start(t); o.stop(t + dur + 0.02);
    },
    waka: function (alt) {
      if (alt) this.tone(540, 300, 0.07, "square", 0.05);
      else this.tone(300, 540, 0.07, "square", 0.05);
    },
    power: function () { this.tone(140, 920, 0.4, "sawtooth", 0.06); },
    eatChaser: function () { this.tone(220, 1250, 0.32, "square", 0.09); },
    bucket: function () {
      this.tone(990, 990, 0.09, "sine", 0.12);
      this.tone(1320, 1320, 0.14, "sine", 0.12, 0.09);
    },
    death: function () {
      var self = this;
      [620, 540, 460, 380, 300, 220, 150, 90].forEach(function (f, i) {
        self.tone(f, f * 0.9, 0.1, "triangle", 0.1, i * 0.09);
      });
    },
    jingle: function () {
      var self = this;
      [523, 659, 784, 1046].forEach(function (f, i) {
        self.tone(f, f, 0.11, "square", 0.07, i * 0.09);
      });
    }
  };

  // ---------------------------------------------------------- dom
  function $(id) { return document.getElementById(id); }
  var wrap = $("gm-wrap"), canvas = $("gm-canvas"), ctx = canvas.getContext("2d");
  var elScore = $("gm-score"), elBest = $("gm-best"), elLevel = $("gm-level"),
      elLives = $("gm-lives"), overlay = $("gm-overlay"),
      panelTitle = $("gm-panel-title"), panelText = $("gm-panel-text"),
      panelScore = $("gm-panel-score"), panelNote = $("gm-panel-note"),
      actionBtn = $("gm-action"), muteBtn = $("gm-mute"),
      pauseBtn = $("gm-pause");
  var IS_MEMBER = wrap && wrap.getAttribute("data-member") === "1";
  var MY_HANDLE = wrap ? (wrap.getAttribute("data-handle") || "") : "";

  // ---------------------------------------------------------- state
  var game = {
    state: "attract",       // attract | playing | paused | gameover
    phase: "ready",          // ready | run | dying | clear (in playing)
    phaseT: 0,
    score: 0, lives: 3, level: 1,
    best: parseInt(localStorage.getItem("gm_best") || "0", 10) || 0,
    fright: 0, chain: 0, eaten: 0,
    bucket: { active: false, t: 0 },
    texts: [],               // floating score popups
    submitted: false,
    shake: 0
  };
  var pellets = new Set(), powers = new Set(), totalPellets = 0;
  function loadPellets() {
    pellets.clear(); powers.clear();
    for (var y = 0; y < ROWS; y++) for (var x = 0; x < COLS; x++) {
      var c = grid[y][x];
      if (c === ".") pellets.add(x + "," + y);
      if (c === "o") powers.add(x + "," + y);
    }
    totalPellets = pellets.size + powers.size;
    game.eaten = 0;
  }

  function makeChaser(kind, x, y, mode, release) {
    return {
      kind: kind, x: x + 0.5, y: y + 0.5,
      dir: DIRS.left, speed: 0, mode: mode,
      release: release, bobPhase: Math.random() * 6.28,
      waypoint: 0
    };
  }
  var player, chasers = [];
  function resetActors() {
    player = {
      x: PLAYER_SPAWN.x + 0.5, y: PLAYER_SPAWN.y + 0.5,
      dir: DIRS.left, want: DIRS.left, speed: 0, mouth: 0
    };
    chasers = [
      makeChaser("frank", 9, 8, "chase", 0),
      makeChaser("vamp", 9, 10, "inpen", 0.4),
      makeChaser("skeleton", 8, 10, "inpen", 2.2),
      makeChaser("witch", 10, 10, "inpen", 4.2)
    ];
  }

  // ---------------------------------------------------------- speeds
  function levelSpeeds() {
    var l = game.level;
    return {
      player: Math.min(7.6 + 0.35 * (l - 1), 11),
      chaser: Math.min(7.0 + 0.35 * (l - 1), 10.5),
      fright: 4.6, eyes: 13.5,
      frightTime: Math.max(7 - 0.6 * (l - 1), 2)
    };
  }

  // ---------------------------------------------------------- movement
  function nextCenter(p, d) {
    return d > 0 ? Math.floor(p + 0.5) + 0.5 : Math.ceil(p - 0.5) - 0.5;
  }
  function atCenter(e) {
    return Math.abs(e.x - (Math.floor(e.x) + 0.5)) < 1e-6 &&
           Math.abs(e.y - (Math.floor(e.y) + 0.5)) < 1e-6;
  }
  // Advance an entity along the grid; chooseDir(e) runs at every tile
  // center and may change e.dir (zeroing it stops the entity).
  function stepEntity(e, dt, chooseDir) {
    var step = e.speed * dt, guard = 0;
    while (step > 1e-9 && guard++ < 10) {
      if (atCenter(e)) {
        chooseDir(e);
        if (e.dir.x === 0 && e.dir.y === 0) return;
      }
      var alongX = e.dir.x !== 0;
      var nc = nextCenter(alongX ? e.x : e.y, alongX ? e.dir.x : e.dir.y);
      var d = Math.abs(nc - (alongX ? e.x : e.y));
      if (d <= 1e-9) { // exactly on the next center: snap and re-decide
        if (alongX) e.x = nc; else e.y = nc;
        continue;
      }
      var m = Math.min(d, step);
      e.x += e.dir.x * m; e.y += e.dir.y * m; step -= m;
      if (m === d) { if (alongX) e.x = nc; else e.y = nc; }
    }
    // tunnel wrap
    if (Math.floor(e.y) === TUNNEL_ROW) {
      if (e.x < 0) e.x += COLS;
      if (e.x >= COLS) e.x -= COLS;
    }
  }
  function tileOf(e) { return { x: Math.floor(e.x), y: Math.floor(e.y) }; }
  function optionsFrom(e, who, mode, allowReverse) {
    var t = tileOf(e), out = [];
    for (var name in DIRS) {
      var d = DIRS[name];
      if (!allowReverse && sameDir(d, rev(e.dir))) continue;
      if (canPass(t.x + d.x, t.y + d.y, who, mode)) out.push(d);
    }
    return out;
  }

  // ---------------------------------------------------------- brains
  function playerChoose(e) {
    var t = tileOf(e);
    if (canPass(t.x + e.want.x, t.y + e.want.y, "player")) e.dir = e.want;
    else if (!canPass(t.x + e.dir.x, t.y + e.dir.y, "player"))
      e.dir = { x: 0, y: 0 };
  }
  var WAYPOINTS = [{ x: 1, y: 1 }, { x: 17, y: 1 }, { x: 17, y: 22 }, { x: 1, y: 22 }];
  function chaserTarget(c) {
    var pt = tileOf(player);
    if (c.kind === "frank") return pt;
    if (c.kind === "vamp") return {
      x: Math.max(0, Math.min(COLS - 1, pt.x + player.dir.x * 4)),
      y: Math.max(0, Math.min(ROWS - 1, pt.y + player.dir.y * 4))
    };
    if (c.kind === "skeleton") {
      var dx = c.x - (pt.x + 0.5), dy = c.y - (pt.y + 0.5);
      if (dx * dx + dy * dy < 25) return pt; // close? pounce
      var wp = WAYPOINTS[c.waypoint % WAYPOINTS.length];
      var wx = c.x - (wp.x + 0.5), wy = c.y - (wp.y + 0.5);
      if (wx * wx + wy * wy < 2.2) c.waypoint++;
      return wp;
    }
    // witch: hunts from afar, shy up close
    var wx2 = c.x - (pt.x + 0.5), wy2 = c.y - (pt.y + 0.5);
    if (wx2 * wx2 + wy2 * wy2 > 64) return pt;
    return { x: 1, y: 22 };
  }
  function chaserChoose(c) {
    var t = tileOf(c);
    if (c.mode === "leaving") {
      if (t.x === DOOR_FRONT.x && t.y === DOOR_FRONT.y) {
        c.mode = "chase"; // out the door: fall through to street logic
        // (straight up from the doorstep is a wall — he must turn)
      } else if (t.x < PEN.x) { c.dir = DIRS.right; return; }
      else if (t.x > PEN.x) { c.dir = DIRS.left; return; }
      else { c.dir = DIRS.up; return; }
    }
    if (c.mode === "entering") {
      if (t.x === PEN.x && t.y === PEN.y) {
        c.mode = "inpen"; c.release = 0.4; c.dir = DIRS.up;
      } else c.dir = DIRS.down;
      return;
    }
    if (c.mode === "eyes") {
      if (t.x === DOOR_FRONT.x && t.y === DOOR_FRONT.y) {
        c.mode = "entering"; c.dir = DIRS.down; return;
      }
      var opts = optionsFrom(c, "chaser", "eyes", true);
      var bestOpt = null, bestD = Infinity;
      opts.forEach(function (d) {
        var k = (t.x + d.x) + "," + (t.y + d.y);
        var dd = doorDist[k] === undefined ? 9999 : doorDist[k];
        if (dd < bestD) { bestD = dd; bestOpt = d; }
      });
      if (bestOpt) c.dir = bestOpt;
      return;
    }
    // street modes: chase behavior, or frightened flight
    var options = optionsFrom(c, "chaser", "chase", false);
    if (!options.length) { c.dir = rev(c.dir); return; }
    if (game.fright > 0) {
      c.dir = options[Math.floor(Math.random() * options.length)];
      return;
    }
    var tgt = chaserTarget(c), bd = Infinity, pick = options[0];
    options.forEach(function (d) {
      var nx = t.x + d.x + 0.5, ny = t.y + d.y + 0.5;
      var dd = (nx - (tgt.x + 0.5)) * (nx - (tgt.x + 0.5)) +
               (ny - (tgt.y + 0.5)) * (ny - (tgt.y + 0.5));
      if (dd < bd) { bd = dd; pick = d; }
    });
    c.dir = pick;
  }

  // ---------------------------------------------------------- flow
  function hud() {
    elScore.textContent = game.score.toLocaleString();
    elBest.textContent = Math.max(game.best, game.score).toLocaleString();
    elLevel.textContent = game.level;
    elLives.textContent = game.lives > 0 ? "\u{1F47B}".repeat(game.lives) : "—";
  }
  function showPanel(title, text, action, scoreLine, note) {
    panelTitle.textContent = title;
    panelText.textContent = text;
    actionBtn.textContent = action;
    if (scoreLine) {
      panelScore.hidden = false; panelScore.textContent = scoreLine;
    } else panelScore.hidden = true;
    if (note) {
      panelNote.hidden = false; panelNote.textContent = note;
    } else panelNote.hidden = true;
    overlay.classList.add("gm-show");
  }
  function hidePanel() { overlay.classList.remove("gm-show"); }

  function startGame() {
    AudioSys.ensure();
    game.score = 0; game.lives = 3; game.level = 1;
    game.submitted = false;
    loadPellets(); resetActors();
    game.state = "playing"; game.phase = "ready"; game.phaseT = 1.0;
    game.fright = 0; game.bucket.active = false;
    hidePanel(); hud(); AudioSys.jingle();
  }
  function nextLevel() {
    game.level++;
    loadPellets(); resetActors();
    game.phase = "ready"; game.phaseT = 1.0; game.fright = 0;
    game.bucket.active = false; hud(); AudioSys.jingle();
  }
  function resetAfterDeath() {
    resetActors();
    game.phase = "ready"; game.phaseT = 0.9; game.fright = 0;
    game.bucket.active = false;
  }
  function gameOver() {
    game.state = "gameover";
    if (game.score > game.best) {
      game.best = game.score;
      localStorage.setItem("gm_best", String(game.best));
    }
    hud();
    var note = "";
    if (IS_MEMBER) {
      note = "Posting your score to the board…";
      submitScore();
    } else {
      note = "Guest best saved on this device. Join HauntSocial to hit the leaderboard.";
    }
    showPanel("Game Over",
      "The monsters got the ghost — but the neighborhood remembers.",
      "Play again",
      "Final score: " + game.score.toLocaleString(), note);
  }
  function submitScore() {
    if (game.submitted || game.score <= 0) {
      if (game.score <= 0) panelNote.textContent = "No score to post this run.";
      return;
    }
    game.submitted = true;
    fetch("/api/games/ghost-maze/score", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ score: game.score })
    }).then(function (r) { return r.ok ? r.json() : null; })
      .then(function (data) {
        if (!data || !data.ok) {
          panelNote.textContent = "Couldn't post that score — your best here is still saved on this device.";
          return;
        }
        var rank = 0;
        data.board.forEach(function (row, i) {
          if (row.handle === MY_HANDLE) rank = i + 1;
        });
        panelNote.textContent = rank > 0
          ? "Score posted — you're #" + rank + " on the board with " + data.best.toLocaleString() + "."
          : "Score posted — your best is " + data.best.toLocaleString() + ". Crack the Top 10 to see your name up there.";
        renderBoard(data.board);
      })
      .catch(function () {
        panelNote.textContent = "Couldn't post that score — your best here is still saved on this device.";
      });
  }
  function renderBoard(board) {
    var list = $("gm-board-list"), empty = $("gm-board-empty");
    if (!list) return;
    list.innerHTML = "";
    board.forEach(function (row) {
      var li = document.createElement("li");
      var a = document.createElement("a");
      a.href = "/@" + row.handle; a.textContent = "@" + row.handle;
      var s = document.createElement("span");
      s.className = "gm-board-score";
      s.textContent = Number(row.best_score).toLocaleString();
      li.appendChild(a); li.appendChild(s); list.appendChild(li);
    });
    if (empty) empty.hidden = board.length > 0;
  }

  // ---------------------------------------------------------- update
  var wakaAlt = false;
  function addText(x, y, text, color) {
    game.texts.push({ x: x, y: y, text: text, color: color || "#f9e5c2", t: 0 });
  }
  function eatAt(tile) {
    var k = tile.x + "," + tile.y;
    if (pellets.has(k)) {
      pellets.delete(k); game.eaten++;
      game.score += 10; wakaAlt = !wakaAlt; AudioSys.waka(wakaAlt);
      if (game.eaten === 70 || game.eaten === 170) {
        game.bucket.active = true; game.bucket.t = 9.5;
      }
      if (pellets.size === 0 && powers.size === 0) {
        game.phase = "clear"; game.phaseT = 1.8;
      }
    } else if (powers.has(k)) {
      powers.delete(k); game.eaten++;
      game.score += 50; game.chain = 0;
      game.fright = levelSpeeds().frightTime;
      chasers.forEach(function (c) {
        if (c.mode === "chase") c.dir = rev(c.dir);
      });
      AudioSys.power();
      if (pellets.size === 0 && powers.size === 0) {
        game.phase = "clear"; game.phaseT = 1.8;
      }
    }
    if (game.bucket.active && tile.x === BUCKET_TILE.x && tile.y === BUCKET_TILE.y) {
      var vals = [100, 300, 500, 700, 1000];
      var v = vals[Math.min(game.level, 5) - 1];
      game.score += v; game.bucket.active = false;
      addText(BUCKET_TILE.x + 0.5, BUCKET_TILE.y + 0.5, "+" + v, "#ff7b1c");
      AudioSys.bucket();
    }
    hud();
  }
  function update(dt) {
    var sp = levelSpeeds();
    // floating texts always drift
    game.texts = game.texts.filter(function (t) {
      t.t += dt; t.y -= dt * 0.7; return t.t < 1.1;
    });
    if (game.phase === "ready") {
      game.phaseT -= dt;
      if (game.phaseT <= 0) game.phase = "run";
      return;
    }
    if (game.phase === "dying") {
      game.phaseT -= dt;
      if (game.phaseT <= 0) {
        if (game.lives <= 0) gameOver(); else resetAfterDeath();
      }
      return;
    }
    if (game.phase === "clear") {
      game.phaseT -= dt;
      if (game.phaseT <= 0) nextLevel();
      return;
    }
    // fright timer
    if (game.fright > 0) game.fright = Math.max(0, game.fright - dt);
    // bucket timer
    if (game.bucket.active) {
      game.bucket.t -= dt;
      if (game.bucket.t <= 0) game.bucket.active = false;
    }
    // player
    player.speed = sp.player;
    player.mouth += dt * 10;
    stepEntity(player, dt, playerChoose);
    eatAt(tileOf(player));
    if (game.phase !== "run") return; // level cleared mid-step
    // chasers
    chasers.forEach(function (c) {
      if (c.mode === "inpen") {
        c.release -= dt;
        if (c.release <= 0) c.mode = "leaving";
        return;
      }
      var t = tileOf(c);
      if (c.mode === "eyes") c.speed = sp.eyes;
      else if (game.fright > 0 && c.mode === "chase") c.speed = sp.fright;
      else c.speed = (t.y === TUNNEL_ROW) ? sp.chaser * 0.55 : sp.chaser;
      stepEntity(c, dt, chaserChoose);
    });
    // collisions
    chasers.forEach(function (c) {
      if (c.mode !== "chase" && c.mode !== "leaving") return;
      var dx = c.x - player.x, dy = c.y - player.y;
      if (dx * dx + dy * dy > 0.30) return;
      if (game.fright > 0 && c.mode === "chase") {
        var pts = [200, 400, 800, 1600][Math.min(game.chain, 3)];
        game.chain++; game.score += pts;
        addText(c.x, c.y, "+" + pts, "#57a8ff");
        c.mode = "eyes"; AudioSys.eatChaser(); hud();
      } else {
        game.lives--; hud();
        game.phase = "dying"; game.phaseT = 1.1;
        AudioSys.death();
      }
    });
  }

  // ---------------------------------------------------------- drawing
  var wallCanvas = document.createElement("canvas");
  wallCanvas.width = COLS * TILE; wallCanvas.height = ROWS * TILE;
  (function drawWalls() {
    var g = wallCanvas.getContext("2d");
    g.fillStyle = "#081a30";
    for (var y = 0; y < ROWS; y++) for (var x = 0; x < COLS; x++) {
      if (grid[y][x] === "#") g.fillRect(x * TILE, y * TILE, TILE, TILE);
    }
    g.strokeStyle = "#57a8ff"; g.lineWidth = 2;
    g.shadowColor = "rgba(87,168,255,0.8)"; g.shadowBlur = 5;
    g.beginPath();
    for (var y2 = 0; y2 < ROWS; y2++) for (var x2 = 0; x2 < COLS; x2++) {
      if (grid[y2][x2] !== "#") continue;
      var px = x2 * TILE, py = y2 * TILE;
      if (cellAt(x2, y2 - 1) !== "#") { g.moveTo(px, py + 1); g.lineTo(px + TILE, py + 1); }
      if (cellAt(x2, y2 + 1) !== "#") { g.moveTo(px, py + TILE - 1); g.lineTo(px + TILE, py + TILE - 1); }
      if (cellAt(x2 - 1, y2) !== "#") { g.moveTo(px + 1, py); g.lineTo(px + 1, py + TILE); }
      if (cellAt(x2 + 1, y2) !== "#") { g.moveTo(px + TILE - 1, py); g.lineTo(px + TILE - 1, py + TILE); }
    }
    g.stroke();
    // house door
    g.shadowBlur = 0; g.fillStyle = "#ff7b1c";
    g.fillRect(DOOR.x * TILE + 2, DOOR.y * TILE + TILE / 2 - 2, TILE - 4, 4);
  })();

  function drawGhostShape(g, cx, cy, r, color, dirX, frightFace, flashWhite, scaleY) {
    g.save();
    g.translate(cx, cy); g.scale(1, scaleY || 1);
    g.fillStyle = color;
    g.beginPath();
    g.moveTo(-r, r);
    g.arc(0, 0, r, Math.PI, 0);
    var waves = 4, w = (2 * r) / waves, t = performance.now() / 130;
    g.lineTo(r, r);
    for (var i = 0; i < waves; i++) {
      var x0 = r - i * w;
      g.quadraticCurveTo(x0 - w * 0.25, r - (Math.sin(t + i) * 2 + 3), x0 - w * 0.5, r);
      g.quadraticCurveTo(x0 - w * 0.75, r + 2, x0 - w, r);
    }
    g.closePath(); g.fill();
    if (frightFace) {
      g.fillStyle = flashWhite ? "#e5484d" : "#f9e5c2";
      g.beginPath(); g.arc(-r * 0.35, -r * 0.2, r * 0.14, 0, 7); g.fill();
      g.beginPath(); g.arc(r * 0.35, -r * 0.2, r * 0.14, 0, 7); g.fill();
      g.strokeStyle = g.fillStyle; g.lineWidth = 1.6; g.beginPath();
      for (var j = 0; j < 3; j++) {
        var mx = -r * 0.45 + j * (r * 0.45);
        g.moveTo(mx, r * 0.32);
        g.quadraticCurveTo(mx + r * 0.11, r * 0.16, mx + r * 0.22, r * 0.32);
      }
      g.stroke();
    }
    g.restore();
  }
  function drawPinEyes(g, cx, cy, r, dir) {
    // the ghost's eyes: little map pins, a nod to the HauntMap mark,
    // drawn fresh here — circle + point, glancing the way he moves.
    [-0.36, 0.36].forEach(function (off) {
      var ex = cx + off * r + dir.x * r * 0.16;
      var ey = cy - r * 0.18 + dir.y * r * 0.16;
      g.fillStyle = "#57a8ff";
      g.beginPath();
      g.arc(ex, ey - r * 0.1, r * 0.21, 0, 7);
      g.moveTo(ex - r * 0.15, ey + r * 0.04);
      g.lineTo(ex + r * 0.15, ey + 0.04);
      g.lineTo(ex, ey + r * 0.3);
      g.closePath(); g.fill();
      g.fillStyle = "#05080a";
      g.beginPath(); g.arc(ex, ey - r * 0.1, r * 0.09, 0, 7); g.fill();
    });
  }
  function drawPlayer(g) {
    var cx = player.x * TILE, cy = player.y * TILE;
    if (game.phase === "dying") {
      var p = 1 - Math.max(game.phaseT, 0) / 1.1;
      drawGhostShape(g, cx, cy, TILE * 0.42 * (1 - p * 0.8), "#f9e5c2",
        player.dir, false, false, 1 - p * 0.4);
      return;
    }
    g.save();
    g.shadowColor = "rgba(87,168,255,0.9)"; g.shadowBlur = 12;
    drawGhostShape(g, cx, cy, TILE * 0.44, "#f9e5c2", player.dir);
    g.restore();
    drawPinEyes(g, cx, cy, TILE * 0.44, player.dir);
  }
  function drawChaser(g, c) {
    var cx = c.x * TILE, cy = c.y * TILE, r = TILE * 0.44;
    if (c.mode === "eyes" || c.mode === "entering") {
      // just the eyes, hurrying home
      g.fillStyle = "#fff";
      [-0.3, 0.3].forEach(function (off) {
        g.beginPath(); g.arc(cx + off * r, cy - r * 0.1, r * 0.2, 0, 7); g.fill();
      });
      g.fillStyle = "#2745e0";
      [-0.3, 0.3].forEach(function (off) {
        g.beginPath();
        g.arc(cx + off * r + c.dir.x * 2, cy - r * 0.1 + c.dir.y * 2, r * 0.1, 0, 7);
        g.fill();
      });
      return;
    }
    var frightened = game.fright > 0 && (c.mode === "chase");
    if (frightened) {
      var flash = game.fright < 1.6 && Math.floor(game.fright * 5) % 2 === 0;
      drawGhostShape(g, cx, cy, r, flash ? "#e8ecff" : "#2b3fd6",
        c.dir, true, flash);
      return;
    }
    var colors = { frank: "#3fae5a", vamp: "#8b5cf6", skeleton: "#e8e6e3", witch: "#5b4a8a" };
    drawGhostShape(g, cx, cy, r, colors[c.kind], c.dir);
    g.save();
    g.translate(cx, cy);
    if (c.kind === "frank") {
      g.fillStyle = "#2c7a40";
      g.fillRect(-r * 0.85, -r * 1.02, r * 1.7, r * 0.3); // flat top
      g.fillStyle = "#cfd6dd";
      g.fillRect(-r * 1.08, r * 0.25, r * 0.22, r * 0.3); // neck bolts
      g.fillRect(r * 0.86, r * 0.25, r * 0.22, r * 0.3);
      g.strokeStyle = "#1d4d2a"; g.lineWidth = 1.4; // stitches
      g.beginPath(); g.moveTo(-r * 0.5, -r * 0.55); g.lineTo(r * 0.5, -r * 0.55); g.stroke();
      g.fillStyle = "#101418";
      g.beginPath(); g.arc(-r * 0.32, -r * 0.15, r * 0.11, 0, 7); g.fill();
      g.beginPath(); g.arc(r * 0.32, -r * 0.15, r * 0.11, 0, 7); g.fill();
    } else if (c.kind === "vamp") {
      g.fillStyle = "#f3e9e2"; // pale face
      g.beginPath(); g.arc(0, -r * 0.28, r * 0.52, 0, 7); g.fill();
      g.fillStyle = "#c1121f";
      g.beginPath(); g.arc(-r * 0.2, -r * 0.32, r * 0.09, 0, 7); g.fill();
      g.beginPath(); g.arc(r * 0.2, -r * 0.32, r * 0.09, 0, 7); g.fill();
      g.fillStyle = "#fff"; // fangs
      g.beginPath();
      g.moveTo(-r * 0.22, r * 0.05); g.lineTo(-r * 0.1, r * 0.05); g.lineTo(-r * 0.16, r * 0.28);
      g.moveTo(r * 0.1, r * 0.05); g.lineTo(r * 0.22, r * 0.05); g.lineTo(r * 0.16, r * 0.28);
      g.fill();
      g.fillStyle = "#5e35b1"; // cape wings
      g.beginPath();
      g.moveTo(-r * 0.95, -r * 0.5); g.lineTo(-r * 1.25, r * 0.7); g.lineTo(-r * 0.55, r * 0.5);
      g.moveTo(r * 0.95, -r * 0.5); g.lineTo(r * 1.25, r * 0.7); g.lineTo(r * 0.55, r * 0.5);
      g.fill();
    } else if (c.kind === "skeleton") {
      g.fillStyle = "#101418"; // eye sockets
      g.beginPath(); g.arc(-r * 0.3, -r * 0.25, r * 0.19, 0, 7); g.fill();
      g.beginPath(); g.arc(r * 0.3, -r * 0.25, r * 0.19, 0, 7); g.fill();
      g.beginPath(); // nose
      g.moveTo(0, -r * 0.02); g.lineTo(-r * 0.09, r * 0.18); g.lineTo(r * 0.09, r * 0.18);
      g.fill();
      g.strokeStyle = "#101418"; g.lineWidth = 1.5; // teeth
      for (var i = -1; i <= 1; i++) {
        g.beginPath(); g.moveTo(i * r * 0.22, r * 0.42); g.lineTo(i * r * 0.22, r * 0.68); g.stroke();
      }
    } else if (c.kind === "witch") {
      g.fillStyle = "#79a86b"; // green face
      g.beginPath(); g.arc(0, -r * 0.2, r * 0.5, 0, 7); g.fill();
      g.fillStyle = "#241a3f"; // pointed hat
      g.beginPath();
      g.moveTo(-r * 0.95, -r * 0.45); g.lineTo(r * 0.95, -r * 0.45);
      g.lineTo(r * 0.15, -r * 1.45); g.lineTo(-r * 0.25, -r * 0.5);
      g.closePath(); g.fill();
      g.fillStyle = "#ff7b1c"; // hat band
      g.fillRect(-r * 0.62, -r * 0.52, r * 1.3, r * 0.14);
      g.fillStyle = "#101418";
      g.beginPath(); g.arc(-r * 0.18, -r * 0.22, r * 0.08, 0, 7); g.fill();
      g.beginPath(); g.arc(r * 0.18, -r * 0.22, r * 0.08, 0, 7); g.fill();
    }
    g.restore();
  }
  function draw(now) {
    ctx.fillStyle = "#05080a";
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    // level-clear flash
    if (game.phase === "clear" && Math.floor(now / 160) % 2 === 0) {
      ctx.fillStyle = "rgba(87,168,255,0.12)";
      ctx.fillRect(0, 0, canvas.width, canvas.height);
    }
    ctx.drawImage(wallCanvas, 0, 0);
    // candy
    ctx.fillStyle = "#f9e5c2";
    pellets.forEach(function (k) {
      var p = k.split(","), x = +p[0], y = +p[1];
      ctx.beginPath();
      ctx.arc(x * TILE + TILE / 2, y * TILE + TILE / 2, 2.4, 0, 7);
      ctx.fill();
    });
    // power pumpkins
    powers.forEach(function (k) {
      var p = k.split(","), x = +p[0], y = +p[1];
      var cx = x * TILE + TILE / 2, cy = y * TILE + TILE / 2;
      var rr = 6.2 + Math.sin(now / 220 + x) * 1.1;
      ctx.save();
      ctx.shadowColor = "rgba(255,123,28,0.9)"; ctx.shadowBlur = 10;
      ctx.fillStyle = "#ff7b1c";
      ctx.beginPath(); ctx.arc(cx, cy, rr, 0, 7); ctx.fill();
      ctx.restore();
      ctx.strokeStyle = "#8a4a12"; ctx.lineWidth = 1.4;
      ctx.beginPath(); ctx.moveTo(cx, cy - rr * 0.6); ctx.lineTo(cx, cy + rr * 0.6); ctx.stroke();
      ctx.fillStyle = "#3fae5a";
      ctx.fillRect(cx - 1.2, cy - rr - 2.5, 2.4, 3.4);
    });
    // candy bucket bonus
    if (game.bucket.active) {
      var bx = BUCKET_TILE.x * TILE + TILE / 2, by = BUCKET_TILE.y * TILE + TILE / 2;
      ctx.save();
      ctx.shadowColor = "rgba(255,123,28,0.9)"; ctx.shadowBlur = 12;
      ctx.fillStyle = "#ff7b1c";
      ctx.beginPath();
      ctx.moveTo(bx - 8, by - 3); ctx.lineTo(bx + 8, by - 3);
      ctx.lineTo(bx + 6, by + 8); ctx.lineTo(bx - 6, by + 8);
      ctx.closePath(); ctx.fill();
      ctx.restore();
      ctx.fillStyle = "#e5484d";
      ctx.beginPath(); ctx.arc(bx - 4, by - 6, 3, 0, 7); ctx.fill();
      ctx.fillStyle = "#57a8ff";
      ctx.beginPath(); ctx.arc(bx + 1, by - 7.5, 3, 0, 7); ctx.fill();
      ctx.fillStyle = "#f9e5c2";
      ctx.beginPath(); ctx.arc(bx + 5.5, by - 5.5, 3, 0, 7); ctx.fill();
    }
    // actors (pen dwellers bob)
    chasers.forEach(function (c) {
      if (c.mode === "inpen") {
        var bob = Math.sin(now / 300 + c.bobPhase) * 2.2;
        var keep = c.y;
        c.y = PEN.y + 0.5 + bob / TILE;
        drawChaser(ctx, c);
        c.y = keep;
      } else drawChaser(ctx, c);
    });
    if (!(game.state === "gameover")) drawPlayer(ctx);
    // floating texts
    game.texts.forEach(function (t) {
      ctx.globalAlpha = Math.max(1 - t.t / 1.1, 0);
      ctx.fillStyle = t.color;
      ctx.font = "700 12px Fredoka, sans-serif";
      ctx.textAlign = "center";
      ctx.fillText(t.text, t.x * TILE, t.y * TILE);
      ctx.globalAlpha = 1;
    });
    if (game.phase === "ready" && game.state === "playing") {
      ctx.fillStyle = "#f9e5c2";
      ctx.font = "700 20px Fredoka, sans-serif";
      ctx.textAlign = "center";
      ctx.fillText(game.level === 1 && game.score === 0 ? "READY?" : "READY?",
        canvas.width / 2, (PLAYER_SPAWN.y - 1.4) * TILE);
    }
    if (game.phase === "clear") {
      ctx.fillStyle = "#57a8ff";
      ctx.font = "700 21px Fredoka, sans-serif";
      ctx.textAlign = "center";
      ctx.fillText("STREET CLEARED!", canvas.width / 2, (PLAYER_SPAWN.y - 1.4) * TILE);
    }
  }

  // ---------------------------------------------------------- loop
  var lastTs = 0;
  function frame(ts) {
    requestAnimationFrame(frame);
    if (!lastTs) lastTs = ts;
    var dt = Math.min((ts - lastTs) / 1000, 0.05);
    lastTs = ts;
    if (game.state === "playing") update(dt);
    draw(ts);
  }

  // ---------------------------------------------------------- input
  function setWant(name) {
    if (player && DIRS[name]) player.want = DIRS[name];
  }
  document.addEventListener("keydown", function (ev) {
    var k = ev.key;
    var dirName = { ArrowUp: "up", ArrowDown: "down", ArrowLeft: "left",
      ArrowRight: "right", w: "up", s: "down", a: "left", d: "right",
      W: "up", S: "down", A: "left", D: "right" }[k];
    if (dirName) { ev.preventDefault(); setWant(dirName); }
    else if (k === " " || k === "Enter") {
      if (game.state === "attract" || game.state === "gameover") {
        ev.preventDefault(); actionBtn.click();
      } else if (game.state === "paused") { ev.preventDefault(); resumeGame(); }
    } else if ((k === "p" || k === "P" || k === "Escape") &&
               game.state === "playing") pauseGame();
    else if (k === "m" || k === "M") muteBtn.click();
  });
  // swipe on the stage
  var touchStart = null;
  var stage = document.querySelector(".gm-stage");
  stage.addEventListener("touchstart", function (ev) {
    var t = ev.changedTouches[0];
    touchStart = { x: t.clientX, y: t.clientY };
  }, { passive: true });
  stage.addEventListener("touchmove", function (ev) {
    if (game.state === "playing") ev.preventDefault();
  }, { passive: false });
  stage.addEventListener("touchend", function (ev) {
    if (!touchStart) return;
    var t = ev.changedTouches[0];
    var dx = t.clientX - touchStart.x, dy = t.clientY - touchStart.y;
    touchStart = null;
    if (Math.abs(dx) < 18 && Math.abs(dy) < 18) return;
    setWant(Math.abs(dx) > Math.abs(dy) ? (dx > 0 ? "right" : "left")
                                        : (dy > 0 ? "down" : "up"));
  });
  // d-pad
  Array.prototype.forEach.call(document.querySelectorAll(".gm-dbtn"),
    function (btn) {
      btn.addEventListener("pointerdown", function (ev) {
        ev.preventDefault(); setWant(btn.getAttribute("data-dir"));
      });
    });
  // buttons
  actionBtn.addEventListener("click", function () {
    if (game.state === "paused") resumeGame();
    else startGame();
  });
  function pauseGame() {
    if (game.state !== "playing") return;
    game.state = "paused";
    showPanel("Paused", "The monsters are holding their breath.",
      "Keep haunting", null, null);
  }
  function resumeGame() {
    if (game.state !== "paused") return;
    game.state = "playing"; hidePanel();
  }
  pauseBtn.addEventListener("click", function () {
    if (game.state === "playing") pauseGame();
    else if (game.state === "paused") resumeGame();
  });
  function paintMute() {
    muteBtn.textContent = AudioSys.muted ? "\u{1F507}" : "\u{1F50A}";
  }
  muteBtn.addEventListener("click", function () {
    AudioSys.muted = !AudioSys.muted;
    localStorage.setItem("gm_muted", AudioSys.muted ? "1" : "0");
    paintMute();
    if (!AudioSys.muted) { AudioSys.ensure(); AudioSys.bucket(); }
  });
  document.addEventListener("visibilitychange", function () {
    if (document.hidden && game.state === "playing") pauseGame();
  });

  // ---------------------------------------------------------- boot
  loadPellets(); resetActors(); hud(); paintMute();
  showPanel("Ghost Maze",
    "Eat all the candy to clear the street. Power pumpkins turn the monsters into snacks — for a few seconds.",
    "Start haunting", null, null);
  requestAnimationFrame(frame);

  // read-only hooks for automated play-tests
  window.GM_DEBUG = {
    game: game,
    get player() { return player; },
    get chasers() { return chasers; },
    get pelletsLeft() { return pellets.size + powers.size; },
    pellets: function () { return Array.from(pellets).concat(Array.from(powers)); },
    start: startGame,
    setDir: setWant
  };
})();
