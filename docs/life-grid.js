/*
 * life-grid.js: an interactive Game of Life grid for the slides.
 *
 *   LifeGrid(container, scene)  builds a canvas with controls inside `container` and returns a
 *   handle { play, pause, reset, step, setActive, fit }.
 *
 * A scene is { cells: [[x, y], ...] | rle: "...", offset: {x, y}, view: {x0, y0, x1, y1},
 *   gens, loop, speed, marks: [{x, y, label}], boxes: [{x0, y0, x1, y1, label, color, from, to}] }.
 * Coordinates: x to the right, y downwards, one unit per cell.
 *
 * Interaction: drag to pan, click to toggle a cell (scenes with `editable`), wheel or the +/- buttons to zoom (about the pointer), "fit" to frame
 * the scene again; play / pause, single step, reset, and a speed slider (generations per second).
 * The rule is B3/S23 on an unbounded grid (sparse 32 x 32 tiles, 32 cells per machine word).
 */
(function () {
  "use strict";
  /* ---------------- The universe: 32 x 32 tiles of bit rows ----------------
   * A tile at (tx, ty) holds the cells 32 tx <= x < 32 tx + 32, 32 ty <= y < 32 ty + 32; bit j of
   * row r is the cell (32 tx + j, 32 ty + r). One generation is computed 32 cells at a time by a
   * bit-sliced adder of the eight neighbour words (the same idea as `nextRow` in LifeSim.lean). */
  const TOFF = 65536, TM = 131072;
  const tkey = (tx, ty) => (tx + TOFF) * TM + (ty + TOFF);

  class Universe {
    constructor(cells) {
      this.tiles = new Map();
      for (const [x, y] of cells) this.set(x, y);
    }
    tile(tx, ty, create) {
      const k = tkey(tx, ty);
      let t = this.tiles.get(k);
      if (!t && create) { t = { tx, ty, rows: new Int32Array(32) }; this.tiles.set(k, t); }
      return t;
    }
    set(x, y) {
      const tx = Math.floor(x / 32), ty = Math.floor(y / 32);
      this.tile(tx, ty, true).rows[y - 32 * ty] |= 1 << (x - 32 * tx);
    }
    toggle(x, y) {
      const tx = Math.floor(x / 32), ty = Math.floor(y / 32);
      this.tile(tx, ty, true).rows[y - 32 * ty] ^= 1 << (x - 32 * tx);
    }
    get size() {
      let n = 0;
      for (const t of this.tiles.values()) for (let r = 0; r < 32; r++) { let v = t.rows[r]; while (v) { v &= v - 1; n++; } }
      return n;
    }
    /** Every live cell, as a callback f(x, y). */
    forEach(f) {
      for (const t of this.tiles.values()) {
        const x0 = 32 * t.tx, y0 = 32 * t.ty;
        for (let r = 0; r < 32; r++) {
          let v = t.rows[r];
          while (v) { const j = 31 - Math.clz32(v & -v); f(x0 + j, y0 + r); v &= v - 1; }
        }
      }
    }
    /** One generation of B3/S23. */
    step() {
      const old = this.tiles;
      // the tiles to compute: every live tile and the neighbours its border touches
      const todo = new Map();
      const want = (tx, ty) => { const k = tkey(tx, ty); if (!todo.has(k)) todo.set(k, [tx, ty]); };
      for (const t of old.values()) {
        const R = t.rows; let any = 0, left = 0, right = 0;
        for (let r = 0; r < 32; r++) { any |= R[r]; left |= R[r] & 1; right |= R[r] & 0x80000000; }
        if (!any) continue;
        const top = R[0] !== 0, bot = R[31] !== 0;
        want(t.tx, t.ty);
        if (top) want(t.tx, t.ty - 1);
        if (bot) want(t.tx, t.ty + 1);
        if (left) { want(t.tx - 1, t.ty); if (R[0] & 1) want(t.tx - 1, t.ty - 1); if (R[31] & 1) want(t.tx - 1, t.ty + 1); }
        if (right) { want(t.tx + 1, t.ty); if (R[0] & 0x80000000) want(t.tx + 1, t.ty - 1); if (R[31] & 0x80000000) want(t.tx + 1, t.ty + 1); }
      }
      const Z = new Int32Array(32);
      const rowsOf = (tx, ty) => { const t = old.get(tkey(tx, ty)); return t ? t.rows : Z; };
      const C = new Int32Array(34), Lb = new Int32Array(34), Rb = new Int32Array(34);
      const next = new Map();
      for (const [k, [tx, ty]] of todo) {
        const M0 = rowsOf(tx, ty), U = rowsOf(tx, ty - 1), D = rowsOf(tx, ty + 1);
        const Lm = rowsOf(tx - 1, ty), Rm = rowsOf(tx + 1, ty);
        const LU = rowsOf(tx - 1, ty - 1), RU = rowsOf(tx + 1, ty - 1);
        const LD = rowsOf(tx - 1, ty + 1), RD = rowsOf(tx + 1, ty + 1);
        C[0] = U[31]; Lb[0] = LU[31] >>> 31; Rb[0] = RU[31] & 1;
        C[33] = D[0]; Lb[33] = LD[0] >>> 31; Rb[33] = RD[0] & 1;
        for (let r = 0; r < 32; r++) { C[r + 1] = M0[r]; Lb[r + 1] = Lm[r] >>> 31; Rb[r + 1] = Rm[r] & 1; }
        const out = new Int32Array(32);
        let nz = 0;
        for (let i = 1; i <= 32; i++) {
          const u = C[i - 1], m = C[i], d = C[i + 1];
          if ((u | m | d | Lb[i - 1] | Lb[i] | Lb[i + 1] | Rb[i - 1] | Rb[i] | Rb[i + 1]) === 0) continue;
          let s0 = 0, s1 = 0, s2 = 0, c;
          // add the eight neighbour words; s2 records a count of four or more
          let x = (u << 1) | Lb[i - 1]; c = s0 & x; s0 ^= x; s2 |= s1 & c; s1 ^= c;
          x = u; c = s0 & x; s0 ^= x; s2 |= s1 & c; s1 ^= c;
          x = (u >>> 1) | (Rb[i - 1] << 31); c = s0 & x; s0 ^= x; s2 |= s1 & c; s1 ^= c;
          x = (m << 1) | Lb[i]; c = s0 & x; s0 ^= x; s2 |= s1 & c; s1 ^= c;
          x = (m >>> 1) | (Rb[i] << 31); c = s0 & x; s0 ^= x; s2 |= s1 & c; s1 ^= c;
          x = (d << 1) | Lb[i + 1]; c = s0 & x; s0 ^= x; s2 |= s1 & c; s1 ^= c;
          x = d; c = s0 & x; s0 ^= x; s2 |= s1 & c; s1 ^= c;
          x = (d >>> 1) | (Rb[i + 1] << 31); c = s0 & x; s0 ^= x; s2 |= s1 & c; s1 ^= c;
          const v = ~s2 & s1 & (s0 | m);
          out[i - 1] = v; nz |= v;
        }
        if (nz) next.set(k, { tx, ty, rows: out });
      }
      this.tiles = next;
    }
    clone() {
      const u = new Universe([]);
      for (const [k, t] of this.tiles) u.tiles.set(k, { tx: t.tx, ty: t.ty, rows: t.rows.slice() });
      return u;
    }
  }

  /** Decode a run-length encoded pattern (standard `b`, `o`, `$`, `!`) at an offset. */
  function parseRLE(rle, ox, oy) {
    const out = [];
    let x = 0, y = 0, n = "";
    // drop the header line (`x = .., y = .., rule = ..`) and comment lines
    const body = rle.split("\n").filter(l => !/^\s*(x\s*=|#)/.test(l)).join("");
    for (const ch of body.replace(/\s+/g, "")) {
      if (ch >= "0" && ch <= "9") { n += ch; continue; }
      const r = n === "" ? 1 : parseInt(n, 10); n = "";
      if (ch === "b" || ch === ".") x += r;
      else if (ch === "o" || ch === "A") { for (let i = 0; i < r; i++) out.push([ox + x + i, oy + y]); x += r; }
      else if (ch === "$") { y += r; x = 0; }
      else if (ch === "!") break;
    }
    return out;
  }

  /** Cells of `ofRows x y rows` exactly as in `Certificates/LifeSim.lean`: bit `j` of row `i` is
   * the cell `(x + j, y + i)` (least significant bit leftmost; `y` grows downwards on screen). */
  function ofRows(x, y, rows) {
    const out = [];
    rows.forEach((r, i) => {
      let b = BigInt(r), j = 0;
      while (b > 0n) { if (b & 1n) out.push([x + j, y + i]); b >>= 1n; j++; }
    });
    return out;
  }

  function sceneCells(scene) {
    if (scene.cells) return scene.cells;
    if (scene.rle) return parseRLE(scene.rle, (scene.offset || {}).x || 0, (scene.offset || {}).y || 0);
    if (scene.parts) return scene.parts.flatMap(sceneCells);
    if (scene.rows) return ofRows(scene.rows[0], scene.rows[1], scene.rows[2]);
    return [];
  }

  function el(tag, cls, text) {
    const e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }

  function LifeGrid(container, scene) {
    container.classList.add("lg");
    container.setAttribute("data-prevent-swipe", "");
    const canvas = el("canvas", "lg-canvas");
    const bar = el("div", "lg-bar");
    const bPlay = el("button", "lg-btn lg-play", "▶");
    const bStep = el("button", "lg-btn", "⏭");
    const bReset = el("button", "lg-btn", "⟲");
    const bIn = el("button", "lg-btn", "+");
    const bOut = el("button", "lg-btn", "−");
    const bFit = el("button", "lg-btn lg-wide", "fit");
    const speed = el("input", "lg-speed");
    speed.type = "range"; speed.min = "0"; speed.max = "130";
    const sLab = el("span", "lg-info");
    const info = el("span", "lg-info lg-gen");
    bPlay.title = "play / pause"; bStep.title = "one generation"; bReset.title = "back to the start";
    bIn.title = "zoom in"; bOut.title = "zoom out"; bFit.title = "frame the scene";
    speed.title = "generations per second";
    bar.append(bPlay, bStep, bReset, el("span", "lg-sep"), bOut, bIn, bFit, el("span", "lg-sep"),
      speed, sLab);
    // jumps to precomputed generations (long runs)
    const snaps = (scene.snapshots || []).map(sn => ({ ...sn, cells: sceneCells(sn) }));
    if (snaps.length) {
      const sel = el("select", "lg-sel");
      sel.append(new Option("jump to…", ""));
      snaps.forEach((sn, i) => sel.append(new Option(sn.label + " (gen " + sn.gen + ")", String(i))));
      sel.onchange = () => {
        if (sel.value === "") return;
        const sn = snaps[Number(sel.value)];
        U = new Universe(sn.cells); gen = sn.gen; sel.value = ""; draw();
      };
      bar.append(sel);
    }
    bar.append(info);
    container.append(canvas);
    if (scene.controls !== false) container.append(bar);
    const ctx = canvas.getContext("2d", { willReadFrequently: true });

    const initCells = sceneCells(scene);
    let U = new Universe(initCells), gen = 0, playing = false, active = false, acc = 0, last = null;
    // the slider position p in [0, 130] gives 2^(p / 10) generations per second (1 .. 8192)
    let gps = scene.speed || 8;
    speed.value = String(Math.round(10 * Math.log2(gps)));
    const showSpeed = () => { sLab.textContent = (gps < 10 ? gps.toFixed(1) : Math.round(gps)) + " gen/s"; };
    showSpeed();
    let scale = 8, ox = 0, oy = 0, W = 0, H = 0;

    function resize() {
      const w = canvas.clientWidth, h = canvas.clientHeight;
      if (w === 0 || h === 0) return false;
      const dpr = Math.min(2, window.devicePixelRatio || 1);
      if (canvas.width !== Math.round(w * dpr) || canvas.height !== Math.round(h * dpr)) {
        canvas.width = Math.round(w * dpr); canvas.height = Math.round(h * dpr);
      }
      W = canvas.width; H = canvas.height;
      return true;
    }

    function fit() {
      if (!resize()) return;
      let v = scene.view;
      if (!v) {
        let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
        U.forEach((x, y) => { x0 = Math.min(x0, x); x1 = Math.max(x1, x); y0 = Math.min(y0, y); y1 = Math.max(y1, y); });
        if (x0 === Infinity) { x0 = -10; y0 = -10; x1 = 10; y1 = 10; }
        v = { x0: x0 - 4, y0: y0 - 4, x1: x1 + 4, y1: y1 + 4 };
      }
      const vw = v.x1 - v.x0 + 1, vh = v.y1 - v.y0 + 1;
      scale = Math.min(W / vw, H / vh);
      ox = (W - vw * scale) / 2 - v.x0 * scale;
      oy = (H - vh * scale) / 2 - v.y0 * scale;
      draw();
    }

    function zoomAt(f, px, py) {
      const ns = Math.max(0.01, Math.min(80, scale * f));
      const r = ns / scale;
      ox = px - (px - ox) * r; oy = py - (py - oy) * r; scale = ns;
      draw();
    }

    const visible = o => (o.from === undefined || gen >= o.from) && (o.to === undefined || gen <= o.to);

    function draw() {
      if (!W) return;
      ctx.fillStyle = "#0b1220";
      ctx.fillRect(0, 0, W, H);
      if (scale >= 9) {
        ctx.strokeStyle = "rgba(154,166,189,0.13)"; ctx.lineWidth = 1;
        ctx.beginPath();
        const gx0 = Math.floor(-ox / scale), gx1 = Math.ceil((W - ox) / scale);
        const gy0 = Math.floor(-oy / scale), gy1 = Math.ceil((H - oy) / scale);
        for (let x = gx0; x <= gx1; x++) { const p = Math.round(x * scale + ox) + 0.5; ctx.moveTo(p, 0); ctx.lineTo(p, H); }
        for (let y = gy0; y <= gy1; y++) { const p = Math.round(y * scale + oy) + 0.5; ctx.moveTo(0, p); ctx.lineTo(W, p); }
        ctx.stroke();
      }
      const fs = Math.round(Math.max(13 * (W / Math.max(1, canvas.clientWidth)), W / 52));
      for (const b of scene.boxes || []) {
        if (!visible(b)) continue;
        const x = b.x0 * scale + ox, y = b.y0 * scale + oy;
        const w = (b.x1 - b.x0 + 1) * scale, h = (b.y1 - b.y0 + 1) * scale;
        ctx.fillStyle = b.fill || "rgba(255,146,43,0.09)";
        ctx.fillRect(x, y, w, h);
        ctx.strokeStyle = b.color || "rgba(255,146,43,0.9)";
        ctx.setLineDash([6, 4]); ctx.lineWidth = Math.max(1, W / 800);
        ctx.strokeRect(x, y, w, h); ctx.setLineDash([]);
        if (b.label) {
          ctx.fillStyle = b.color || "#ffa94d";
          ctx.font = "600 " + fs + "px 'Source Sans 3', sans-serif";
          ctx.textAlign = "left"; ctx.fillText(b.label, x + 3, y - 6);
        }
      }
      const col = scene.color || "#66d9e8";
      if (scale >= 1.5) {
        ctx.fillStyle = col;
        const g = scale >= 6 ? Math.max(1, scale * 0.12) : 0, sz = Math.max(1, scale - g);
        U.forEach((cx, cy) => {
          const x = cx * scale + ox, y = cy * scale + oy;
          if (x < -scale || y < -scale || x > W || y > H) return;
          ctx.fillRect(x + g / 2, y + g / 2, sz, sz);
        });
      } else {
        // zoomed out: one or two device pixels per live cell
        const img = ctx.getImageData(0, 0, W, H), d = img.data;
        const c = parseInt(col.slice(1), 16), cr = c >> 16, cg = (c >> 8) & 255, cb = c & 255;
        const dot = Math.max(1, Math.round(Math.min(W, H) / 250));
        U.forEach((cx, cy) => {
          const x = Math.floor(cx * scale + ox), y = Math.floor(cy * scale + oy);
          for (let a = 0; a < dot; a++) for (let b = 0; b < dot; b++) {
            const X = x + a, Y = y + b;
            if (X < 0 || Y < 0 || X >= W || Y >= H) continue;
            const i = (Y * W + X) * 4;
            d[i] = cr; d[i + 1] = cg; d[i + 2] = cb; d[i + 3] = 255;
          }
        });
        ctx.putImageData(img, 0, 0);
      }
      ctx.font = "600 " + fs + "px 'Source Sans 3', sans-serif";
      for (const m of scene.marks || []) {
        if (!visible(m)) continue;
        const x = (m.x + 0.5) * scale + ox, y = (m.y + 0.5) * scale + oy;
        const rad = Math.max(W / 120, (m.r || 3) * scale);
        ctx.strokeStyle = m.color || "rgba(255,212,59,0.95)"; ctx.lineWidth = Math.max(1.5, W / 700);
        ctx.beginPath(); ctx.arc(x, y, rad, 0, Math.PI * 2); ctx.stroke();
        ctx.fillStyle = m.color || "#ffd43b"; ctx.textAlign = "center";
        ctx.fillText(m.label, x, y - rad - 6);
      }
      info.textContent = "gen " + gen.toLocaleString("en") + " · " + U.size.toLocaleString("en") + " cells";
    }

    function stepOnce() {
      U.step(); gen++;
      if (scene.gens && gen >= scene.gens) {
        if (scene.loop === false) setPlaying(false);
        else { U = new Universe(initCells); gen = 0; }
      }
    }

    function setPlaying(p) { playing = p; bPlay.textContent = p ? "⏸" : "▶"; last = null; }
    function reset() { U = new Universe(initCells); gen = 0; acc = 0; draw(); }

    function frame(ts) {
      if (!active) return;
      if (playing) {
        if (last !== null) {
          acc += Math.min(0.1, (ts - last) / 1000) * gps;
          const t0 = performance.now();
          while (acc >= 1 && playing && performance.now() - t0 < 28) { stepOnce(); acc -= 1; }
          if (acc > 2) acc = 0;
        }
        last = ts;
        draw();
      }
      requestAnimationFrame(frame);
    }

    bPlay.onclick = () => setPlaying(!playing);
    bStep.onclick = () => { setPlaying(false); stepOnce(); draw(); };
    bReset.onclick = reset;
    bIn.onclick = () => zoomAt(1.5, W / 2, H / 2);
    bOut.onclick = () => zoomAt(1 / 1.5, W / 2, H / 2);
    bFit.onclick = fit;
    speed.oninput = () => { gps = Math.pow(2, Number(speed.value) / 10); showSpeed(); };

    const toCanvas = e => {
      const r = canvas.getBoundingClientRect();
      return [(e.clientX - r.left) * W / r.width, (e.clientY - r.top) * H / r.height];
    };
    canvas.addEventListener("wheel", e => {
      e.preventDefault(); e.stopPropagation();
      const [px, py] = toCanvas(e);
      zoomAt(Math.exp(-e.deltaY * 0.0015), px, py);
    }, { passive: false });
    let drag = null;
    canvas.addEventListener("pointerdown", e => {
      drag = { p: toCanvas(e), ox, oy, moved: false };
      canvas.setPointerCapture(e.pointerId); e.stopPropagation();
    });
    canvas.addEventListener("pointermove", e => {
      if (!drag) return;
      const [px, py] = toCanvas(e);
      if (Math.abs(px - drag.p[0]) + Math.abs(py - drag.p[1]) > 4) drag.moved = true;
      ox = drag.ox + px - drag.p[0]; oy = drag.oy + py - drag.p[1];
      draw();
    });
    canvas.addEventListener("pointerup", e => {
      // a click without dragging toggles a cell (in editable scenes)
      if (drag && !drag.moved && scene.editable) {
        const [px, py] = toCanvas(e);
        U.toggle(Math.floor((px - ox) / scale), Math.floor((py - oy) / scale));
        draw();
      }
      drag = null;
    });
    canvas.addEventListener("pointercancel", () => { drag = null; });
    if (!scene.editable) canvas.addEventListener("dblclick", e => { const [px, py] = toCanvas(e); zoomAt(2, px, py); });
    bar.addEventListener("keydown", e => e.stopPropagation());

    let fitted = false;
    function setActive(a) {
      if (a === active) return;
      active = a;
      if (a) {
        if (!fitted) { fitted = resize(); fit(); } else { resize(); draw(); }
        if (scene.autoplay !== false && !playing) setPlaying(true);
        requestAnimationFrame(frame);
      } else {
        setPlaying(false);
      }
    }
    window.addEventListener("resize", () => { if (active) { resize(); draw(); } });
    return { play: () => setPlaying(true), pause: () => setPlaying(false), reset, fit, setActive,
      step: () => { stepOnce(); draw(); } };
  }

  window.LifeGrid = LifeGrid;
  window.LifeGrid.Universe = Universe;
  window.LifeGrid.parseRLE = parseRLE;
  window.LifeGrid.ofRows = ofRows;
  window.LifeGrid.sceneCells = sceneCells;
})();
