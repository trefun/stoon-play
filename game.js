// stoon: UI, ink rendering, CPU turn flow.
(function () {
  'use strict';

  const { t } = window.StoonI18n;
  const { PASS, EMPTY, BLACK, WHITE } = window.Stoon;
  // Board size follows the level: よわい is played on 5x5, the others on 7x7.
  const BOARDS = {
    5: { komi: 3.5, stars: [[2, 2]] },
    7: { komi: 7.5, stars: [[3, 3], [1, 1], [5, 1], [1, 5], [5, 5]] },
  };
  let S, N, POINTS, idx, xOf, yOf, KOMI;
  const MOVE_LIMIT = 120;
  const LEVELS = {
    easy: { size: 5, iters: 1500, temperature: 0.7, shy: true, resign: false, handicapKomi: 0.5, offCenter: true },
    // handicapKomi: komi the CPU gets when it plays second (a little help for you).
    normal: { size: 7, iters: 2500, temperature: 0.3, floor: 0.5, resign: true, handicapKomi: 4.5 },
    strong: { size: 7, iters: 14000, temperature: 0, resign: true },
  };
  const ANALYSIS_ITERS = 2500;
  const FINAL_ITERS = 14000;
  const CONFIRM_ITERS = 6000; // estimate with the other side to move before ending on its own
  const CPU_MIN_MS = 550;

  // Ink match-ups: [you, CPU]. One is drawn at launch, for each rematch and on
  // returning to the title.
  const INK_PAIRS = [
    ['#343bc4', '#df6624'], ['#1a1aaf', '#e38d24'], ['#3a0ced', '#d0bf08'],
    ['#6325cd', '#bfcd41'], ['#6e04b6', '#cd510a'], ['#9025c6', '#efb121'],
    ['#ba30b0', '#a0e937'], ['#c12d74', '#2eb721'], ['#c43a6e', '#1bbfab'],
    ['#d74b31', '#1ee0ad'],
  ];

  const COLORS = {};
  let pairIndex = -1;

  function hexRgb(h) { return [1, 3, 5].map((i) => parseInt(h.slice(i, i + 2), 16)); }
  function rgbHex(c) { return '#' + c.map((v) => Math.round(Math.max(0, Math.min(255, v))).toString(16).padStart(2, '0')).join(''); }
  function mix(h, to, k) { const a = hexRgb(h), b = hexRgb(to); return rgbHex(a.map((v, i) => v + (b[i] - v) * k)); }
  function luminance(h) {
    const [r, g, b] = hexRgb(h).map((v) => { v /= 255; return v <= 0.03928 ? v / 12.92 : Math.pow((v + 0.055) / 1.055, 2.4); });
    return 0.2126 * r + 0.7152 * g + 0.0722 * b;
  }

  function pickInks(forced) {
    let i = forced;
    if (i == null) {
      do { i = (Math.random() * INK_PAIRS.length) | 0; } while (i === pairIndex && INK_PAIRS.length > 1);
    }
    pairIndex = i;
    const root = document.documentElement.style;
    for (const [side, base] of [['me', INK_PAIRS[i][0]], ['cpu', INK_PAIRS[i][1]]]) {
      const light = mix(base, '#ffffff', 0.5);
      const deep = mix(base, '#000000', 0.2);
      const dark = mix(base, '#000000', 0.5);
      // Readable on the dark background, and text color on top of the ink.
      const text = mix(base, '#ffffff', luminance(base) > 0.3 ? 0.15 : 0.45);
      const on = luminance(base) > 0.35 ? '#120b28' : '#ffffff';
      COLORS[side] = base;
      COLORS[side + 'Light'] = light;
      COLORS[side + 'Deep'] = deep;
      COLORS[side + 'Text'] = text;
      COLORS[side + 'On'] = on;
      root.setProperty('--' + side, base);
      root.setProperty('--' + side + '-light', light);
      root.setProperty('--' + side + '-deep', deep);
      root.setProperty('--' + side + '-dark', dark);
      root.setProperty('--' + side + '-text', text);
      root.setProperty('--' + side + '-on', on);
    }
  }
  // ?ink=1..10 fixes the first match-up (for checking colors).
  let inkParam = null;
  try { inkParam = parseInt(new URLSearchParams(location.search).get('ink'), 10) - 1; } catch (e) { /* ignore */ }
  pickInks(inkParam >= 0 && inkParam < INK_PAIRS.length ? inkParam : null);

  // Your color this game (black moves first; white gets komi).
  let you = BLACK;
  // Japanese counting: territory (empty points) + prisoners (アゲハマ) + komi.
  const prisoners = { [BLACK]: 0, [WHITE]: 0 }; // stones captured by each color
  const trayShown = { me: 0, cpu: 0 }; // what the trays show (lags behind flying stones)
  const sideOf = (color) => (color === you ? 'me' : 'cpu');
  const toMe = (v) => (you === BLACK ? v : -v); // black-positive -> you-positive

  // Circles [x, y, r] (in cell units around grid coordinates) that paint point p for an
  // owner map: the point itself, bridges to same-owner neighbours, fillers for 2x2
  // blocks, and spill-over past the board edge.
  function puddleCircles(p, owner) {
    const o = owner[p];
    const gx = xOf(p), gy = yOf(p);
    const same = (dx, dy) => {
      const x = gx + dx, y = gy + dy;
      return x >= 0 && y >= 0 && x < N && y < N && owner[idx(x, y)] === o;
    };
    const out = [[gx, gy, 0.62]];
    if (same(1, 0)) out.push([gx + 0.5, gy, 0.54]);
    if (same(0, 1)) out.push([gx, gy + 0.5, 0.54]);
    if (same(-1, 0)) out.push([gx - 0.5, gy, 0.54]);
    if (same(0, -1)) out.push([gx, gy - 0.5, 0.54]);
    for (const [dx, dy] of [[1, 1], [1, -1], [-1, 1], [-1, -1]]) {
      if (same(dx, 0) && same(0, dy) && same(dx, dy)) out.push([gx + dx / 2, gy + dy / 2, 0.52]);
    }
    if (gx === 0) out.push([gx - 0.6, gy, 0.66]);
    if (gx === N - 1) out.push([gx + 0.6, gy, 0.66]);
    if (gy === 0) out.push([gx, gy - 0.6, 0.66]);
    if (gy === N - 1) out.push([gx, gy + 0.6, 0.66]);
    return out;
  }

  function useSize(n) {
    S = window.Stoon.size(n);
    ({ N, POINTS, idx, xOf, yOf } = S);
    KOMI = BOARDS[n].komi;
    MARGIN = n <= 5 ? 88 : 72;
    CELL = (VB - 2 * MARGIN) / (N - 1);
    shown = new Float32Array(S.SIZE);
    target = new Float32Array(S.SIZE);
    finalOwner = new Int8Array(S.SIZE);
    const label = $('board');
    if (label) label.setAttribute('aria-label', t('boardLabel', { n }));
  }

  // Board geometry in SVG units. The 5x5 board keeps a wider rim, so its big edge stones
  // stay on the board.
  const VB = 800;
  let MARGIN = 72, CELL;
  const px = (p) => MARGIN + xOf(p) * CELL;
  const py = (p) => MARGIN + yOf(p) * CELL;

  const $ = (id) => document.getElementById(id);
  const svgNS = 'http://www.w3.org/2000/svg';
  function el(tag, attrs, parent) {
    const e = document.createElementNS(svgNS, tag);
    for (const k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }

  // Deterministic random for decorations.
  function rng(seed) {
    let s = seed >>> 0 || 1;
    return () => {
      s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0;
      return s / 4294967296;
    };
  }

  // Organic ink splat outline centred on (cx, cy).
  function splatPath(cx, cy, r, seed, spikes = 13) {
    const rand = rng(seed);
    const pts = [];
    for (let i = 0; i < spikes; i++) {
      const a = (i / spikes) * Math.PI * 2 + rand() * 0.3;
      const long = rand() < 0.25;
      const rr = r * (long ? 1.15 + rand() * 0.35 : 0.78 + rand() * 0.22);
      pts.push([cx + Math.cos(a) * rr, cy + Math.sin(a) * rr]);
    }
    let d = '';
    for (let i = 0; i < pts.length; i++) {
      const p0 = pts[i], p1 = pts[(i + 1) % pts.length];
      const mx = (p0[0] + p1[0]) / 2, my = (p0[1] + p1[1]) / 2;
      if (i === 0) {
        const pl = pts[pts.length - 1];
        d += `M${((pl[0] + p0[0]) / 2).toFixed(1)},${((pl[1] + p0[1]) / 2).toFixed(1)}`;
      }
      d += `Q${p0[0].toFixed(1)},${p0[1].toFixed(1)} ${mx.toFixed(1)},${my.toFixed(1)}`;
    }
    return d + 'Z';
  }

  function splatGroup(parent, cx, cy, r, color, seed, delay) {
    const g = el('g', { class: 'sp', style: `animation-delay:${delay || 0}s` }, parent);
    el('path', { d: splatPath(cx, cy, r, seed), fill: color }, g);
    const rand = rng(seed * 7 + 3);
    const drops = 4 + ((rand() * 4) | 0);
    for (let i = 0; i < drops; i++) {
      const a = rand() * Math.PI * 2;
      const dist = r * (1.25 + rand() * 0.7);
      el('circle', { cx: cx + Math.cos(a) * dist, cy: cy + Math.sin(a) * dist, r: r * (0.05 + rand() * 0.1), fill: color }, g);
    }
    return g;
  }

  // ---------- persistence (optional) ----------

  const store = {
    get(k, d) { try { const v = localStorage.getItem('stoon.' + k); return v == null ? d : v; } catch (e) { return d; } },
    set(k, v) { try { localStorage.setItem('stoon.' + k, v); } catch (e) { /* ignore */ } },
  };

  // ---------- sound ----------

  const sound = {
    ctx: null,
    muted: store.get('muted', '0') === '1',
    noise: null,
    ensure() {
      if (this.ctx) { if (this.ctx.state === 'suspended') this.ctx.resume(); return; }
      const AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return;
      this.ctx = new AC();
      const len = this.ctx.sampleRate * 0.4;
      this.noise = this.ctx.createBuffer(1, len, this.ctx.sampleRate);
      const d = this.noise.getChannelData(0);
      for (let i = 0; i < len; i++) d[i] = Math.random() * 2 - 1;
    },
    // Wet "pecha": a sharp hit, a gurgling burst of filtered noise, a low thud and a
    // few flying droplets. Slightly randomised so repeated moves don't sound identical.
    splat(pitch = 1, vol = 1) {
      if (this.muted || !this.ctx) return;
      const c = this.ctx, t = c.currentTime + 0.005;
      const jit = (a) => 1 + (Math.random() * 2 - 1) * a;
      const pt = pitch * jit(0.08);
      const out = c.createGain();
      out.gain.value = 0.65 * vol;
      const lp = c.createBiquadFilter();
      lp.type = 'lowpass';
      lp.frequency.value = 7000;
      out.connect(lp).connect(c.destination);

      const noise = (start, dur) => {
        const src = c.createBufferSource();
        src.buffer = this.noise;
        src.start(start, Math.random() * 0.2);
        src.stop(start + dur);
        return src;
      };

      // 1. "p": a very short bright click as the ink lands.
      const hp = c.createBiquadFilter();
      hp.type = 'highpass';
      hp.frequency.value = 2500;
      const cg = c.createGain();
      cg.gain.setValueAtTime(0.5, t);
      cg.gain.exponentialRampToValueAtTime(0.001, t + 0.012);
      noise(t, 0.015).connect(hp).connect(cg).connect(out);

      // 2. "echa": resonant noise sweeping down, chopped by a fast wobble for wetness.
      const bp = c.createBiquadFilter();
      bp.type = 'bandpass';
      bp.Q.value = 2.6;
      bp.frequency.setValueAtTime(2100 * pt, t);
      bp.frequency.exponentialRampToValueAtTime(420 * pt, t + 0.13);
      const env = c.createGain();
      env.gain.setValueAtTime(0.0001, t);
      env.gain.exponentialRampToValueAtTime(0.9, t + 0.006);
      env.gain.exponentialRampToValueAtTime(0.25, t + 0.06);
      env.gain.exponentialRampToValueAtTime(0.0001, t + 0.2);
      const am = c.createGain();
      am.gain.value = 0.6;
      const lfo = c.createOscillator();
      lfo.frequency.setValueAtTime(48 * jit(0.2), t);
      lfo.frequency.linearRampToValueAtTime(22, t + 0.2);
      const lfoDepth = c.createGain();
      lfoDepth.gain.value = 0.4;
      lfo.connect(lfoDepth).connect(am.gain);
      lfo.start(t);
      lfo.stop(t + 0.22);
      noise(t, 0.22).connect(bp).connect(env).connect(am).connect(out);

      // 3. Low thud of the splat hitting the floor.
      const o = c.createOscillator();
      o.type = 'sine';
      o.frequency.setValueAtTime(190 * pt, t);
      o.frequency.exponentialRampToValueAtTime(55 * pt, t + 0.09);
      const og = c.createGain();
      og.gain.setValueAtTime(0.5, t);
      og.gain.exponentialRampToValueAtTime(0.0001, t + 0.11);
      o.connect(og).connect(out);
      o.start(t);
      o.stop(t + 0.12);

      // 4. Droplets: tiny falling blips scattered just after the hit.
      const drops = 3 + ((Math.random() * 3) | 0);
      for (let i = 0; i < drops; i++) {
        const dt = t + 0.03 + Math.random() * 0.12;
        const f = (1300 + Math.random() * 1500) * pt;
        const d = c.createOscillator();
        d.type = 'sine';
        d.frequency.setValueAtTime(f, dt);
        d.frequency.exponentialRampToValueAtTime(f * 0.55, dt + 0.03);
        const dg = c.createGain();
        dg.gain.setValueAtTime(0.0001, dt);
        dg.gain.exponentialRampToValueAtTime(0.1 + Math.random() * 0.08, dt + 0.003);
        dg.gain.exponentialRampToValueAtTime(0.0001, dt + 0.035);
        d.connect(dg).connect(out);
        d.start(dt);
        d.stop(dt + 0.04);
      }
    },
    // One synth note. opts: bend (end freq), vib [rate, depth], cutoff (lowpass Hz, or [from, to]).
    tone(freq, start, dur, type = 'square', vol = 0.18, opts = {}) {
      const c = this.ctx, t = c.currentTime + start;
      const o = c.createOscillator();
      o.type = type;
      o.frequency.setValueAtTime(freq, t);
      if (opts.bend) o.frequency.exponentialRampToValueAtTime(opts.bend, t + dur);
      if (opts.vib) {
        const l = c.createOscillator(), lg = c.createGain();
        l.frequency.value = opts.vib[0];
        lg.gain.value = opts.vib[1];
        l.connect(lg).connect(o.frequency);
        l.start(t);
        l.stop(t + dur + 0.05);
      }
      let node = o;
      if (opts.cutoff) {
        const f = c.createBiquadFilter();
        f.type = 'lowpass';
        f.Q.value = opts.q || 6;
        const [a, b] = Array.isArray(opts.cutoff) ? opts.cutoff : [opts.cutoff, opts.cutoff];
        f.frequency.setValueAtTime(a, t);
        f.frequency.exponentialRampToValueAtTime(b, t + dur);
        node = o.connect(f);
      }
      const g = c.createGain();
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(vol, t + 0.01);
      g.gain.setValueAtTime(vol, t + Math.max(0.01, dur - 0.06));
      g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
      node.connect(g).connect(c.destination);
      o.start(t);
      o.stop(t + dur + 0.02);
    },

    // Match start: two ready beeps, then a rising "go" with a splash.
    start() {
      if (this.muted || !this.ctx) return;
      this.tone(784, 0, 0.09, 'square', 0.12);
      this.tone(784, 0.2, 0.09, 'square', 0.12);
      this.tone(1046, 0.42, 0.4, 'sawtooth', 0.12, { bend: 1568, cutoff: [1800, 6000] });
      this.tone(1318, 0.42, 0.4, 'square', 0.07, { bend: 1976 });
      setTimeout(() => this.splat(1.15, 0.9), 430);
      setTimeout(() => this.splat(0.9, 0.7), 520);
    },

    // Game over: a referee-style warble.
    whistle() {
      if (this.muted || !this.ctx) return;
      this.tone(2300, 0, 0.18, 'sine', 0.16, { vib: [32, 140] });
      this.tone(2300, 0.24, 0.42, 'sine', 0.16, { vib: [32, 140] });
    },

    // Win: bouncy arpeggio up into a held chord, with splashes.
    win() {
      if (this.muted || !this.ctx) return;
      const seq = [523, 659, 784, 1046, 784, 1046];
      seq.forEach((f, i) => this.tone(f, i * 0.09, 0.1, 'square', 0.11, { cutoff: 5000 }));
      const end = seq.length * 0.09;
      [1046, 1318, 1568].forEach((f) => this.tone(f, end, 0.7, 'sawtooth', 0.06, { vib: [6, 8], cutoff: [3000, 1600] }));
      this.tone(262, end, 0.7, 'triangle', 0.18);
      setTimeout(() => this.splat(1.2, 0.8), end * 1000);
      setTimeout(() => this.splat(1.0, 0.6), end * 1000 + 120);
    },

    // Lose: a sagging three-step fall and a "wah-wah".
    lose() {
      if (this.muted || !this.ctx) return;
      [392, 370, 349].forEach((f, i) => this.tone(f, i * 0.24, 0.22, 'triangle', 0.16, { bend: f * 0.97 }));
      this.tone(330, 0.75, 0.32, 'sawtooth', 0.13, { bend: 300, cutoff: [1400, 250], q: 8 });
      this.tone(300, 1.1, 0.6, 'sawtooth', 0.13, { bend: 220, cutoff: [1400, 180], q: 8, vib: [5, 6] });
    },

    notes(freqs, step = 0.11, type = 'triangle') {
      if (this.muted || !this.ctx) return;
      const c = this.ctx, t0 = c.currentTime + 0.02;
      freqs.forEach((f, i) => {
        const t = t0 + i * step;
        const o = c.createOscillator();
        o.type = type;
        o.frequency.value = f;
        const g = c.createGain();
        g.gain.setValueAtTime(0.0001, t);
        g.gain.exponentialRampToValueAtTime(0.22, t + 0.01);
        g.gain.exponentialRampToValueAtTime(0.0001, t + step * 1.8);
        o.connect(g).connect(c.destination);
        o.start(t);
        o.stop(t + step * 2);
      });
    },
  };

  // A short buzz on phones that have it (off together with the sound).
  function buzz(pattern) {
    if (sound.muted || !navigator.vibrate) return;
    try { navigator.vibrate(pattern); } catch (e) { /* ignore */ }
  }

  // ---------- board view ----------

  const boardSvg = $('board');
  const inkSvg = $('board-ink');
  let finalOwner; // +1 you, -1 CPU, as points get counted
  let inkLayers, tileLayer, hintLayer, stoneLayer, fxLayer, ghost, lastMark;
  const inkCircles = { me: [], cpu: [] }; // per point: [{el, base, kind}]
  let shown, target; // displayed / wanted ownership per point
  const stoneEls = new Map(); // point -> {g, color}

  // The ink lives in its own SVG under the board so that stones, splashes and counting
  // animations don't force the heavy ink filter to be redrawn every frame.
  function buildBoard() {
    inkSvg.textContent = '';
    const inkDefs = el('defs', {}, inkSvg);
    inkDefs.innerHTML = `
      <filter id="goo" x="-10%" y="-10%" width="120%" height="120%" color-interpolation-filters="sRGB">
        <feGaussianBlur in="SourceGraphic" stdDeviation="13" result="b"/>
        <feColorMatrix in="b" mode="matrix" values="1 0 0 0 0  0 1 0 0 0  0 0 1 0 0  0 0 0 24 -10" result="g"/>
        <!-- Gloss without lighting (lighting made every ink frame several times slower):
             the softened shape, shifted, leaves a band just inside the edge: pale where
             the puddle faces the top left, dark where it faces away. The edge itself
             keeps the ink color, so it stays crisp. -->
        <feGaussianBlur in="g" stdDeviation="6" result="soft"/>
        <feColorMatrix in="soft" mode="matrix" values="0 0 0 0 0  0 0 0 0 0  0 0 0 0 0  0 0 0 12 -8.4" result="inner"/>
        <feOffset in="soft" dx="7" dy="9" result="sd"/>
        <feComposite in="inner" in2="sd" operator="arithmetic" k1="-1" k2="1" k3="0" k4="0" result="rimTop"/>
        <feOffset in="soft" dx="-5" dy="-7" result="su"/>
        <feComposite in="inner" in2="su" operator="arithmetic" k1="-1" k2="1" k3="0" k4="0" result="rimLow"/>
        <feFlood flood-color="#ffffff" flood-opacity="0.62"/>
        <feComposite in2="rimTop" operator="in" result="shine"/>
        <feFlood flood-color="#120b28" flood-opacity="0.16"/>
        <feComposite in2="rimLow" operator="in" result="shade"/>
        <feMerge><feMergeNode in="g"/><feMergeNode in="shade"/><feMergeNode in="shine"/></feMerge>
      </filter>
      <filter id="goo-lite" x="-10%" y="-10%" width="120%" height="120%" color-interpolation-filters="sRGB">
        <feGaussianBlur in="SourceGraphic" stdDeviation="13" result="b"/>
        <feColorMatrix in="b" mode="matrix" values="1 0 0 0 0  0 1 0 0 0  0 0 1 0 0  0 0 0 24 -10"/>
      </filter>
      <clipPath id="floor-clip"><rect x="14" y="14" width="${VB - 28}" height="${VB - 28}" rx="44"/></clipPath>
      <pattern id="floor-tex" width="90" height="90" patternUnits="userSpaceOnUse">
        <rect width="90" height="90" fill="#e9e5f0"/>
        <circle cx="14" cy="22" r="2.2" fill="#d9d3e3"/>
        <circle cx="61" cy="9" r="1.6" fill="#d9d3e3"/>
        <circle cx="44" cy="58" r="2.6" fill="#ddd7e7"/>
        <circle cx="80" cy="71" r="1.8" fill="#d6d0e1"/>
        <circle cx="25" cy="80" r="1.4" fill="#d9d3e3"/>
      </pattern>`;

    boardSvg.textContent = '';
    const defs = el('defs', {}, boardSvg);
    defs.innerHTML = `
      <radialGradient id="stone-shade">
        <stop offset="0.78" stop-color="#120b28" stop-opacity="0.5"/>
        <stop offset="1" stop-color="#120b28" stop-opacity="0"/>
      </radialGradient>
      <radialGradient id="grad-me" cx="0.36" cy="0.32" r="0.75">
        <stop offset="0" stop-color="${COLORS.meLight}"/>
        <stop offset="0.6" stop-color="${COLORS.me}"/>
        <stop offset="1" stop-color="${COLORS.meDeep}"/>
      </radialGradient>
      <radialGradient id="grad-cpu" cx="0.36" cy="0.32" r="0.75">
        <stop offset="0" stop-color="${COLORS.cpuLight}"/>
        <stop offset="0.6" stop-color="${COLORS.cpu}"/>
        <stop offset="1" stop-color="${COLORS.cpuDeep}"/>
      </radialGradient>`;

    el('rect', { x: 14, y: 22, width: VB - 28, height: VB - 28, rx: 44, fill: '#0c0720', opacity: 0.55 }, inkSvg);
    el('rect', { x: 14, y: 14, width: VB - 28, height: VB - 28, rx: 44, fill: 'url(#floor-tex)' }, inkSvg);

    const clip = el('g', { 'clip-path': 'url(#floor-clip)' }, inkSvg);
    // A touch lighter than the stones: wet ink catching the light (the same lift the
    // old lighting gave flat ink).
    const lift = (h) => rgbHex(hexRgb(h).map((v) => v + 36));
    const inkMe = lift(COLORS.me), inkCpu = lift(COLORS.cpu);
    inkLayers = {
      me: el('g', { fill: inkMe }, clip),
      cpu: el('g', { fill: inkCpu }, clip),
    };
    tileLayer = {
      me: el('g', { fill: inkMe }, clip),
      cpu: el('g', { fill: inkCpu }, clip),
    };
    applyInkQuality();
    finalOwner.fill(0);
    for (const side of ['me', 'cpu']) {
      inkCircles[side] = [];
      for (const p of POINTS) {
        const rand = rng(p * 97 + (side === 'me' ? 11 : 53));
        const list = [{ el: el('circle', { cx: px(p), cy: py(p), r: 0 }, inkLayers[side]), base: 0.74 }];
        for (let k = 0; k < 3; k++) {
          const a = rand() * Math.PI * 2;
          const dist = CELL * (0.42 + rand() * 0.22);
          list.push({ el: el('circle', { class: 'sat', cx: px(p) + Math.cos(a) * dist, cy: py(p) + Math.sin(a) * dist, r: 0 }, inkLayers[side]), base: 0.16 + rand() * 0.12 });
        }
        inkCircles[side][p] = list;
      }
    }

    const grid = el('g', { stroke: '#2a1f4d', 'stroke-opacity': 0.38, 'stroke-width': 4, 'stroke-linecap': 'round' }, boardSvg);
    for (let i = 0; i < N; i++) {
      const v = MARGIN + i * CELL;
      el('line', { x1: MARGIN, y1: v, x2: VB - MARGIN, y2: v }, grid);
      el('line', { x1: v, y1: MARGIN, x2: v, y2: VB - MARGIN }, grid);
    }
    for (const [x, y] of BOARDS[N].stars) {
      el('circle', { cx: MARGIN + x * CELL, cy: MARGIN + y * CELL, r: 9, fill: '#2a1f4d', 'fill-opacity': 0.45 }, boardSvg);
    }

    hintLayer = el('g', { 'pointer-events': 'none' }, boardSvg);
    ghost = el('circle', { class: 'ghost', r: CELL * 0.43, fill: 'url(#grad-me)', cx: -100, cy: -100 }, boardSvg);
    stoneLayer = el('g', {}, boardSvg);
    lastMark = el('circle', { r: 10, fill: '#fff', stroke: '#120b28', 'stroke-width': 4, cx: -100, cy: -100, 'pointer-events': 'none' }, boardSvg);
    fxLayer = el('g', { 'pointer-events': 'none' }, boardSvg);
    stoneEls.clear();
    inkDrawn.me = [];
    inkDrawn.cpu = [];
    inkDry = false;
    shown.fill(0);
    target.fill(0);
  }

  function makeStone(p, color) {
    const side = sideOf(color);
    // The shadow is a soft gradient disc, not a filter: stones shake and bounce a lot,
    // and a filtered group is redrawn through the filter on every frame of that.
    const g = el('g', { class: 'stone drop' }, stoneLayer);
    el('circle', { cx: px(p), cy: py(p) + CELL * 0.07, r: CELL * 0.53, fill: 'url(#stone-shade)' }, g);
    el('circle', { cx: px(p), cy: py(p), r: CELL * 0.43, fill: `url(#grad-${side})`, stroke: '#120b28', 'stroke-width': 5 }, g);
    el('ellipse', { cx: px(p) - CELL * 0.2, cy: py(p) - CELL * 0.24, rx: CELL * 0.08, ry: CELL * 0.05, fill: '#fff', opacity: 0.85, transform: `rotate(-35 ${px(p) - CELL * 0.2} ${py(p) - CELL * 0.24})` }, g);
    setTimeout(() => g.classList.remove('drop'), 450);
    const st = { g, color, face: null, mood: -1 };
    stoneEls.set(p, st);
    setFace(st, p, 0);
    return g;
  }

  // ---------- faces ----------
  // 0 smiling, 1 worried (two liberties or leaning lost), 2 panicking (in atari or
  // about to die), 3 knocked out (counted dead at the end), 4 beaming (two eyes: it can
  // never be taken).
  function setFace(st, p, mood) {
    if (st.mood === mood) return;
    const first = st.mood < 0;
    st.mood = mood;
    if (st.face) st.face.remove();
    const r = CELL * 0.43, cx = px(p), cy = py(p);
    const ink = mood === 3 ? '#120b28' : COLORS[sideOf(st.color) + 'On'];
    const f = el('g', { class: `face mood${mood}` + (first ? '' : ' changed'), fill: 'none', stroke: ink, 'stroke-linecap': 'round', 'stroke-linejoin': 'round', 'stroke-width': r * 0.09 }, st.g);
    const P = (x, y) => `${(cx + x * r).toFixed(1)},${(cy + y * r).toFixed(1)}`;
    const path = (d, extra) => el('path', Object.assign({ d }, extra || {}), f);
    // Plain dot eyes and soft pink cheeks.
    const eyeDot = (x) => el('circle', { cx: cx + x * r, cy: cy - 0.06 * r, r: 0.09 * r, fill: ink, stroke: 'none' }, f);
    const cheeks = () => {
      for (const x of [-0.46, 0.46]) el('ellipse', { cx: cx + x * r, cy: cy + 0.12 * r, rx: 0.13 * r, ry: 0.075 * r, fill: '#ff8fb3', opacity: 0.6, stroke: 'none' }, f);
    };
    const sweat = (x, y) => path(`M${P(x, y - 0.16)}Q${P(x + 0.11, y + 0.02)} ${P(x, y + 0.08)}Q${P(x - 0.11, y + 0.02)} ${P(x, y - 0.16)}Z`,
      { fill: '#8fdcff', stroke: 'none' });
    if (mood === 0) {
      cheeks();
      eyeDot(-0.3); eyeDot(0.3);
      path(`M${P(-0.13, 0.2)}Q${P(0, 0.32)} ${P(0.13, 0.2)}`);
    } else if (mood === 1) {
      cheeks();
      eyeDot(-0.28); eyeDot(0.28);
      path(`M${P(-0.12, 0.28)}Q${P(0, 0.2)} ${P(0.12, 0.28)}`);
      sweat(0.58, -0.32);
    } else if (mood === 2) {
      cheeks();
      path(`M${P(-0.4, -0.18)}L${P(-0.2, -0.06)}L${P(-0.4, 0.06)}M${P(0.4, -0.18)}L${P(0.2, -0.06)}L${P(0.4, 0.06)}`);
      path(`M${P(-0.12, 0.26)}L${P(0.12, 0.26)}`);
      sweat(0.6, -0.36);
      // All panicking stones shiver in step, so the board is still in between.
      st.g.style.setProperty('--sync', -(performance.now() % 2200) + 'ms');
      st.g.classList.add('panic');
    } else if (mood === 4) {
      cheeks();
      path(`M${P(-0.4, 0)}Q${P(-0.3, -0.2)} ${P(-0.2, 0)}M${P(0.2, 0)}Q${P(0.3, -0.2)} ${P(0.4, 0)}`);
      path(`M${P(-0.16, 0.17)}Q${P(0, 0.36)} ${P(0.16, 0.17)}`);
    } else {
      path(`M${P(-0.4, -0.18)}L${P(-0.18, 0.04)}M${P(-0.18, -0.18)}L${P(-0.4, 0.04)}M${P(0.18, -0.18)}L${P(0.4, 0.04)}M${P(0.4, -0.18)}L${P(0.18, 0.04)}`);
      path(`M${P(-0.18, 0.28)}L${P(0.18, 0.28)}`);
    }
    if (mood !== 2) st.g.classList.remove('panic');
    st.face = f;
  }

  // Mood of every stone from its group's liberties and how the estimate sees it.
  // The estimate part only moves when a search has finished (fromEstimate) and needs a
  // clear margin to get better again, so faces don't flip back and forth between moves.
  function updateFaces(fromEstimate) {
    if (state === 'judging' || state === 'over') return;
    const safe = new Set();
    for (const g of twoEyed(board)) for (const q of g.stones) safe.add(q);
    hintLayer.textContent = '';
    const seen = new Set();
    const rings = new Set(); // whose stones are in atari, for the first-time hint
    for (const p of POINTS) {
      const v = board.c[p];
      if (v === EMPTY || seen.has(p)) continue;
      const grp = board.group(p);
      const mine = (q) => (v === you ? target[q] : -target[q]);
      let lean = 0, held = 0;
      const libs = new Set();
      for (const q of grp.stones) {
        seen.add(q);
        lean += mine(q);
        const st = stoneEls.get(q);
        if (st) held = Math.max(held, st.leanMood || 0);
        for (const d of [1, -1, S.W, -S.W]) if (board.c[q + d] === EMPTY) libs.add(q + d);
      }
      lean /= grp.stones.length;
      let libLean = 0;
      for (const q of libs) libLean += mine(q);
      libLean = libs.size ? libLean / libs.size : -1;
      let leanMood = held;
      if (fromEstimate) {
        // m: margin added to every threshold (0 to get worse, 0.2 to get better).
        const moodAt = (m) => {
          if (lean < -0.35 + m || (grp.libs <= 2 && libLean < -0.1 + m) || (grp.libs <= 3 && libLean < -0.4 + m)) return 2;
          if (lean < m || libLean < m) return 1;
          return 0;
        };
        const worse = moodAt(0), better = moodAt(0.2);
        leanMood = worse > held ? worse : better < held ? better : held;
      }
      const libMood = grp.libs >= 3 ? 0 : grp.libs === 2 ? 1 : 2;
      const mood = safe.has(p) ? 4 : Math.max(libMood, leanMood);
      for (const q of grp.stones) {
        const st = stoneEls.get(q);
        if (st) { st.leanMood = leanMood; setFace(st, q, mood); }
      }
      // In atari: a ring on the last liberty, in the ink of whoever can take it there.
      if (libs.size === 1) {
        const [lib] = libs;
        if (lib !== board.ko) { markAtari(lib, 3 - v); rings.add(v); }
      }
    }
    // A ko you cannot retake yet.
    if (board.ko >= 0 && board.turn === you) markKo(board.ko);
    // The first rings ever seen on this device get a word on what they mean: on your turn,
    // once its estimate is in, after any message still up (the opening one, say), and only
    // if the board is still the same then.
    if (fromEstimate && state === 'player') {
      for (const [v, key] of [[3 - you, 'atariTheirs'], [you, 'atariMine']]) {
        if (!rings.has(v) || store.get('seen-' + key, '0') === '1') continue;
        const gen = gameGen, moves = board.moves;
        setTimeout(() => {
          if (gen !== gameGen || state !== 'player' || board.moves !== moves) return;
          store.set('seen-' + key, '1');
          toast(t(key), 3200);
        }, $('toast').classList.contains('show') ? 1600 : 0);
        break;
      }
    }
  }

  function markKo(p) {
    const g = el('g', { class: 'ko-mark' }, hintLayer);
    const w = CELL * 0.62, h = CELL * 0.34;
    el('rect', { x: px(p) - w / 2, y: py(p) - h / 2, width: w, height: h, rx: h / 2, fill: '#120b28', 'fill-opacity': 0.85, stroke: '#fff', 'stroke-width': 3, 'stroke-dasharray': '7 6' }, g);
    const text = el('text', { x: px(p), y: py(p), 'text-anchor': 'middle', 'dominant-baseline': 'central', fill: '#fff', 'font-size': CELL * 0.21, 'font-family': cssVar('--font-head') || 'sans-serif' }, g);
    text.textContent = t('koMark');
  }

  function markAtari(p, taker) {
    const g = el('g', { class: 'atari', fill: 'none', 'stroke-dasharray': '11 10', 'stroke-linecap': 'round', style: `--sync:${-(performance.now() % 2200)}ms` }, hintLayer);
    el('circle', { cx: px(p), cy: py(p), r: CELL * 0.3, stroke: '#120b28', 'stroke-width': 14 }, g);
    el('circle', { cx: px(p), cy: py(p), r: CELL * 0.3, stroke: taker === you ? COLORS.meLight : COLORS.cpuLight, 'stroke-width': 7 }, g);
  }

  // Groups that live on two eyes: two empty areas only they surround, every point of
  // which touches the group, so the other side can never fill both. [{stones, eyes}]
  function twoEyed(b) {
    const out = [];
    for (const g of S.groupsOf(b)) {
      if (g.eyes.length < 2) continue;
      const libs = new Set();
      for (const q of g.stones) for (const d of [1, -1, S.W, -S.W]) if (b.c[q + d] === EMPTY) libs.add(q + d);
      const real = g.eyes.filter((e) => e.every((q) => libs.has(q)));
      if (real.length >= 2) out.push({ stones: g.stones, eyes: real });
    }
    return out;
  }

  function splash(p, color, count = 9, power = 1) {
    const fill = color === you ? COLORS.me : COLORS.cpu;
    for (let i = 0; i < count; i++) {
      const a = Math.random() * Math.PI * 2;
      const dist = CELL * (0.5 + Math.random() * 0.55) * power;
      const r = CELL * (0.05 + Math.random() * 0.08);
      const c = el('circle', { cx: px(p), cy: py(p), r, fill }, fxLayer);
      particles.push({ c, x0: px(p), y0: py(p), dx: Math.cos(a) * dist, dy: Math.sin(a) * dist, r, t: 0, life: 0.38 + Math.random() * 0.2 });
    }
    wake();
  }

  const particles = [];

  // Sync stone elements with the board. Newly placed stones drop in; removed ones pop.
  function syncStones(board, placed) {
    for (const [p, s] of stoneEls) {
      if (board.c[p] !== s.color) {
        s.g.classList.remove('drop');
        s.g.classList.add('pop');
        const g = s.g;
        setTimeout(() => g.remove(), 340);
        stoneEls.delete(p);
        splash(p, 3 - s.color, 6, 0.8);
        target[p] = s.color === you ? -1 : 1;
      }
    }
    for (const p of POINTS) {
      const v = board.c[p];
      if (v !== EMPTY && !stoneEls.has(p)) {
        makeStone(p, v);
        if (p === placed) {
          splash(p, v, 10, 1);
          target[p] = v === you ? 1 : -1;
          shown[p] = target[p] * 0.8;
        }
      }
    }
    updateFaces();
    wake();
    const last = board.last;
    if (last !== PASS && board.c[last] !== EMPTY) {
      // On the stone's upper-right rim: clearly that stone's, and on the board on the top row.
      lastMark.setAttribute('cx', px(last) + CELL * 0.31);
      lastMark.setAttribute('cy', py(last) - CELL * 0.31);
      stoneLayer.appendChild(lastMark);
    } else {
      lastMark.setAttribute('cx', -100);
    }
  }

  function setTarget(own) {
    for (const p of POINTS) target[p] = Math.max(-1, Math.min(1, toMe(own[p])));
    wake();
  }

  // Ownership -> ink size. Weak leans stay unpainted so only real influence shows.
  function inkAmount(v) {
    const t = Math.max(0, Math.min(1, (v - 0.2) / 0.55));
    return Math.sqrt(t);
  }

  // Eases the ink toward the estimate over about a third of a second, whatever the
  // frame rate; true while it is still moving. Every ink change sends the whole ink
  // layer through its filter again, so only circles that changed are touched, and the
  // ink moves only when the estimate does (once per turn, and where a stone lands).
  function renderInk(dt) {
    if (inkDry) return false;
    const k = 1 - Math.exp(-dt / 0.085);
    let moving = false;
    for (const p of POINTS) {
      const d = target[p] - shown[p];
      if (Math.abs(d) > 0.01) { shown[p] += d * k; moving = true; }
      else shown[p] = target[p];
    }
    if (!moving && !inkForce) return false;
    inkForce = false;
    // Without the filter nothing melts the circles together: bigger main circles close
    // the gaps (the small splash circles are hidden then).
    const grow = inkQuality === 0 ? 1.28 : 1;
    for (const p of POINTS) {
      const a = Math.round(inkAmount(shown[p]) * 64) / 64;
      const b = Math.round(inkAmount(-shown[p]) * 64) / 64;
      if (a === inkDrawn.me[p] && b === inkDrawn.cpu[p]) continue;
      inkDrawn.me[p] = a;
      inkDrawn.cpu[p] = b;
      inkCircles.me[p][0].el.setAttribute('r', (CELL * 0.74 * grow * a).toFixed(1));
      inkCircles.cpu[p][0].el.setAttribute('r', (CELL * 0.74 * grow * b).toFixed(1));
      for (let k = 1; k < 4; k++) {
        inkCircles.me[p][k].el.setAttribute('r', (CELL * inkCircles.me[p][k].base * a).toFixed(1));
        inkCircles.cpu[p][k].el.setAttribute('r', (CELL * inkCircles.cpu[p][k].base * b).toFixed(1));
      }
    }
    return moving;
  }
  const inkDrawn = { me: [], cpu: [] }; // ink amounts last written, per point
  let inkForce = false;
  let inkDry = false; // counting: the ink layer is hidden and no longer redrawn

  // Ink quality follows the device: 2 glossy, 1 flat (no gloss), 0 no filter at all
  // (plain circles). While the ink moves, slow frames step it down for this visit.
  // A step down is remembered on this device, so the next visit starts there.
  const savedFx = parseInt(store.get('fx', '2'), 10);
  let inkQuality = savedFx >= 0 && savedFx <= 2 ? savedFx : 2;
  // ?fx=0..2 pins it (for checking the looks).
  let inkPinned = false;
  try {
    const fx = new URLSearchParams(location.search).get('fx');
    if (fx === '0' || fx === '1' || fx === '2') { inkQuality = +fx; inkPinned = true; }
  } catch (e) { /* ignore */ }
  const inkFrames = [];
  function applyInkQuality() {
    const f = inkQuality === 2 ? 'url(#goo)' : inkQuality === 1 ? 'url(#goo-lite)' : null;
    for (const g of [inkLayers.me, inkLayers.cpu, tileLayer.me, tileLayer.cpu]) {
      if (f) g.setAttribute('filter', f);
      else g.removeAttribute('filter');
    }
    inkSvg.classList.toggle('plain', !f);
    inkDrawn.me = [];
    inkDrawn.cpu = [];
    inkForce = true;
    wake();
  }
  function watchInkFrame(dt) {
    if (inkPinned || inkQuality === 0 || document.hidden) return;
    inkFrames.push(dt);
    if (inkFrames.length < 24) return;
    const sorted = inkFrames.slice().sort((a, b) => a - b);
    inkFrames.length = 0;
    if (sorted[12] > 0.045) {
      inkQuality--;
      store.set('fx', String(inkQuality));
      applyInkQuality();
    }
  }

  // The frame loop only runs while something moves (the ink easing, splash drops), so
  // an idle page does no work at all. wake() starts it.
  let lastFrame = 0, frameId = 0;
  function wake() {
    if (frameId) return;
    lastFrame = performance.now();
    frameId = requestAnimationFrame(frame);
  }
  function frame(now) {
    frameId = 0;
    const dt = Math.min(0.1, (now - lastFrame) / 1000 || 0.016);
    lastFrame = now;
    const inkMoving = renderInk(dt);
    if (inkMoving && dt < 0.1) watchInkFrame(dt);
    for (let i = particles.length - 1; i >= 0; i--) {
      const q = particles[i];
      q.t += dt;
      const k = Math.min(1, q.t / q.life);
      const e = 1 - Math.pow(1 - k, 3);
      q.c.setAttribute('cx', (q.x0 + q.dx * e).toFixed(1));
      q.c.setAttribute('cy', (q.y0 + q.dy * e + 30 * k * k).toFixed(1));
      q.c.setAttribute('r', (q.r * (1 - k * 0.6)).toFixed(1));
      q.c.setAttribute('opacity', (1 - k * k).toFixed(2));
      if (k >= 1) { q.c.remove(); particles.splice(i, 1); }
    }
    if (inkMoving || particles.length) frameId = requestAnimationFrame(frame);
  }

  // ---------- prisoners (アゲハマ) ----------

  function renderTray(side) {
    const n = trayShown[side];
    $('tray-' + side + '-n').textContent = n;
    const box = $('tray-' + side + '-stones');
    const show = Math.min(n, 8);
    while (box.children.length < show) box.appendChild(document.createElement('i'));
    while (box.children.length > show) box.lastChild.remove();
  }

  function resetTrays() {
    prisoners[BLACK] = prisoners[WHITE] = 0;
    trayShown.me = trayShown.cpu = 0;
    renderTray('me');
    renderTray('cpu');
  }

  // A captured stone flies from the board into the capturer's tray, then the count ticks.
  function flyToTray(p, stoneColor) {
    const side = stoneColor === you ? 'cpu' : 'me'; // the capturer's tray
    const box = $('tray-' + side + '-stones');
    const r = boardSvg.getBoundingClientRect();
    const k = r.width / VB;
    const size = CELL * 0.86 * k;
    const x = r.left + px(p) * k, y = r.top + py(p) * k;
    const to = box.getBoundingClientRect();
    const tx = (side === 'me' ? to.left + 8 : to.right - 8), ty = to.top + to.height / 2;
    const f = document.createElement('div');
    f.className = 'flyer ' + sideOf(stoneColor);
    f.style.cssText = `left:${x - size / 2}px;top:${y - size / 2}px;width:${size}px;height:${size}px`;
    document.body.appendChild(f);
    requestAnimationFrame(() => requestAnimationFrame(() => {
      f.style.transform = `translate(${tx - x}px, ${ty - y}px) scale(${14 / size})`;
    }));
    let landed = false;
    const land = () => {
      if (landed) return;
      landed = true;
      f.remove();
      trayShown[side]++;
      renderTray(side);
      const tray = $('tray-' + side);
      tray.classList.remove('bump');
      void tray.offsetWidth;
      tray.classList.add('bump');
    };
    f.addEventListener('transitionend', land);
    setTimeout(land, 900);
  }

  function capture(capturer, points) {
    if (!points.length) return;
    prisoners[capturer] += points.length;
    for (const q of points) flyToTray(q, 3 - capturer);
  }

  // ---------- HUD ----------

  const statusEl = $('status');
  function setStatus(text, cls, dots) {
    statusEl.className = 'status ' + (cls || '');
    statusEl.textContent = '';
    // Whose turn: their stone beside the words (the CPU's looks up while it reads).
    if (cls === 'me' || cls === 'cpu') {
      statusEl.insertAdjacentHTML('beforeend', `<svg class="turn-stone" viewBox="-13 -13 26 26" aria-hidden="true">${stoneSvg(0, 0, 11, cls, dots ? 'think' : 'smile')}</svg>`);
    }
    statusEl.appendChild(document.createTextNode(text));
    if (dots) {
      const s = document.createElement('span');
      s.className = 'dots';
      s.innerHTML = '<i>.</i><i>.</i><i>.</i>';
      statusEl.appendChild(s);
    }
    // One line always: long notes shrink to fit instead of pushing the board down.
    statusEl.style.fontSize = '';
    let size = parseFloat(getComputedStyle(statusEl).fontSize);
    while (statusEl.scrollWidth > statusEl.clientWidth + 1 && size > 11) statusEl.style.fontSize = --size + 'px';
  }

  // Toasts sit over the status line while playing (the buttons and the board stay
  // free), above the buttons on the result screen, low on the title.
  let toastTimer = 0, toastHeld = false;
  // A short message over the status line. Its bottom edge sits at the line's bottom, so a
  // two-line message grows up into the free space instead of over the prisoner trays (and
  // in landscape it stays over the side column). held: it belongs to a two-tap confirm and
  // goes away with it.
  function toast(text, ms = 1700, held = false) {
    const el = $('toast');
    el.textContent = text;
    const visible = (e) => e.offsetParent !== null && e.getClientRects().length > 0;
    let x = innerWidth / 2, y = innerHeight - 60, w = innerWidth - 24, down = false;
    const overStatus = visible(statusEl);
    if (overStatus) {
      const r = statusEl.getBoundingClientRect();
      x = r.left + r.width / 2;
      w = Math.min(Math.max(r.width, 260), innerWidth - 24);
      // In the side column (landscape) the meter is right above: grow down instead.
      down = r.width < innerWidth * 0.6;
      y = down ? r.top : r.bottom;
    } else if (visible($('result-actions'))) {
      y = $('result-actions').getBoundingClientRect().top - 10;
    }
    el.style.setProperty('--x', Math.round(x) + 'px');
    el.style.setProperty('--y', Math.round(y) + 'px');
    el.style.setProperty('--w', Math.round(w) + 'px');
    el.classList.toggle('down', down);
    el.classList.add('show');
    // The status line steps aside while a toast covers it.
    document.body.classList.toggle('toasting', overStatus);
    toastHeld = held;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(hideToast, ms);
  }
  function hideToast() {
    clearTimeout(toastTimer);
    $('toast').classList.remove('show');
    document.body.classList.remove('toasting');
    toastHeld = false;
  }

  // own: black-positive estimate; final: {black, white} counted points. Komi goes to white.
  function updateMeter(own, final) {
    let black, white;
    if (final) {
      black = final.black;
      white = final.white;
    } else {
      // Expected territory + prisoners: an empty point is worth 1 to its owner, a stone
      // that dies is worth 2 to the other side (its point and the prisoner).
      black = prisoners[BLACK];
      white = prisoners[WHITE];
      for (const p of POINTS) {
        const v = board ? board.c[p] : EMPTY, o = own[p];
        if (v === EMPTY) { black += (1 + o) / 2; white += (1 - o) / 2; }
        else if (v === WHITE) black += 1 + o;
        else white += 1 - o;
      }
    }
    const meBoard = you === BLACK ? black : white;
    const cpuBoard = you === BLACK ? white : black;
    const meKomi = you === WHITE ? KOMI : 0, cpuKomi = you === BLACK ? KOMI : 0;
    const me = meBoard + meKomi, cpu = cpuBoard + cpuKomi;
    $('meter-me').style.flexGrow = meBoard.toFixed(2);
    $('meter-me-komi').style.flexGrow = meKomi;
    $('meter-cpu-komi').style.flexGrow = cpuKomi;
    $('meter-cpu').style.flexGrow = cpuBoard.toFixed(2);
    $('num-me').textContent = final ? me : Math.round(me);
    $('num-cpu').textContent = final ? cpu : Math.round(cpu);
  }

  // ---------- thinking ----------
  // Searches run in web workers when the page can start them, so stones and ink keep
  // moving while the CPU reads; otherwise here, in short slices between frames.
  // think() resolves with what S.decide needs ({ownership(), ranked(), count, komi}),
  // or never when stopThinking() comes first.

  let thinkGen = 0;
  let jobId = 0;
  const pool = []; // {worker, job}
  const waiting = []; // jobs for the next free worker
  const POOL_SIZE = Math.max(1, Math.min(2, (navigator.hardwareConcurrency || 2) - 1));
  let workersOk = typeof Worker === 'function' && location.protocol !== 'file:';

  function think(b, iters, onProgress) {
    return new Promise((resolve) => {
      const job = { id: ++jobId, gen: thinkGen, n: N, board: b.clone(), komi: KOMI, iters, onProgress, resolve };
      if (workersOk) { waiting.push(job); pump(); } else runHere(job);
    });
  }

  function stopThinking() {
    thinkGen++;
    waiting.length = 0;
    for (const slot of pool) {
      if (slot.job) { slot.worker.postMessage({ type: 'stop', id: 0 }); slot.job = null; }
    }
  }

  function pump() {
    while (waiting.length) {
      let slot = pool.find((s) => !s.job);
      if (!slot && pool.length < POOL_SIZE) slot = spawn();
      if (!workersOk || !slot) return;
      const job = waiting.shift();
      if (job.gen !== thinkGen) continue;
      slot.job = job;
      const b = job.board;
      slot.worker.postMessage({
        type: 'search', id: job.id, n: job.n, komi: job.komi, iters: job.iters, progress: !!job.onProgress,
        seed: (Math.random() * 4294967296) >>> 0,
        board: { c: b.c, turn: b.turn, ko: b.ko, passes: b.passes, moves: b.moves, last: b.last, prisoners: b.prisoners },
      });
    }
  }

  function spawn() {
    let worker;
    try { worker = new Worker('worker.js'); } catch (e) { giveUp(); return null; }
    const slot = { worker, job: null };
    worker.onmessage = (e) => {
      const m = e.data, job = slot.job;
      if (!job || m.id !== job.id) return;
      const own = m.own;
      if (m.type === 'progress') {
        if (job.gen === thinkGen) job.onProgress({ ownership: () => own, count: m.count });
        return;
      }
      slot.job = null;
      if (job.gen === thinkGen) job.resolve({ ownership: () => own, ranked: () => m.ranked, count: m.count, komi: job.komi });
      pump();
    };
    worker.onerror = (e) => { if (e.preventDefault) e.preventDefault(); giveUp(); };
    pool.push(slot);
    return slot;
  }

  // No workers here (opened from a file, a sandboxed frame): run everything on the page.
  function giveUp() {
    if (!workersOk) return;
    workersOk = false;
    const jobs = pool.map((s) => s.job).filter(Boolean).concat(waiting.splice(0));
    for (const slot of pool) slot.worker.terminate();
    pool.length = 0;
    for (const job of jobs) if (job.gen === thinkGen) runHere(job);
  }

  function runHere(job) {
    const search = new (window.Stoon.size(job.n).Search)(job.board, job.komi);
    let lastShow = 0;
    function step() {
      if (job.gen !== thinkGen) return;
      const end = performance.now() + 12;
      while (search.count < job.iters && performance.now() < end) search.run(50);
      if (search.count >= job.iters) { job.resolve(search); return; }
      const now = performance.now();
      if (job.onProgress && now - lastShow > 90) { lastShow = now; job.onProgress(search); }
      setTimeout(step, 0);
    }
    setTimeout(step, 0);
  }

  const wait = (ms) => new Promise((r) => setTimeout(r, Math.max(0, ms)));

  // ---------- game flow ----------

  let board = null;
  let state = 'idle'; // player | cpu | judging | over
  let level = store.get('level', 'easy');
  // A shared link (?level=strong) opens with that level picked.
  try {
    const q = new URLSearchParams(location.search).get('level');
    if (LEVELS[q]) level = q;
  } catch (e) { /* ignore */ }
  if (!LEVELS[level]) level = 'easy';
  let lastResult = null;
  let endReason = '';
  let gameGen = 0; // bumped by every new game and by leaving one: stale steps stop
  let yourOwn = null; // the finished estimate of your current turn

  // pos (for checks): {rows: ['X.O..', ...], you: 'X' | 'O'} starts from that position
  // with you to move.
  function startGame(pos) {
    if (pos && !pos.rows) pos = null;
    sound.ensure();
    stopThinking();
    gameGen++;
    if (pos && LEVELS[level].size !== pos.rows.length) level = pos.rows.length === 5 ? 'easy' : 'normal';
    useSize(LEVELS[level].size);
    board = new S.Board();
    buildBoard();
    inkForce = true;
    wake();
    lastResult = null;
    $('title').hidden = true;
    $('game').hidden = false;
    $('game').classList.remove('over', 'judging');
    $('stamp').classList.remove('show');
    $('level-chip').textContent = `${t(level)} · ${t('sizeShort', { n: N })}`;
    $('howto-open').classList.remove('nudge');
    enter($('game'));
    disarm();
    you = pos ? (pos.you === 'O' ? WHITE : BLACK) : Math.random() < 0.5 ? BLACK : WHITE;
    resetTrays();
    if (you === BLACK && LEVELS[level].handicapKomi != null) KOMI = LEVELS[level].handicapKomi;
    $('komi-me').hidden = you !== WHITE;
    $('komi-cpu').hidden = you !== BLACK;
    if (pos) {
      pos.rows.forEach((row, y) => [...row].forEach((ch, x) => { board.c[idx(x, y)] = ch === 'X' ? BLACK : ch === 'O' ? WHITE : EMPTY; }));
      board.turn = you;
      board.moves = 30;
      syncStones(board, -1);
    }
    updateMeter(new Float32Array(S.SIZE));
    toast(you === BLACK ? t('youFirst', { komi: KOMI }) : t('youSecond', { komi: KOMI }));
    sound.start();
    if (board.turn === you) playerTurn();
    else cpuTurn();
  }

  function playerTurn() {
    state = 'player';
    yourOwn = null;
    // The very first move of someone's first game gets a hint instead.
    const first = board.moves < 2 && !Object.keys(loadRecord()).length;
    setStatus(t(first ? 'tapToPlay' : 'yourTurn'), 'me');
    $('pass').disabled = false;
    $('resign').disabled = false;
    analyze();
  }

  // The meter, the ink and the faces follow the estimate with you to move only: the
  // side to move always looks a little better, so mixing in the CPU's own search would
  // swing them back and forth every move.
  async function analyze() {
    const s = await think(board, ANALYSIS_ITERS);
    const own = s.ownership();
    yourOwn = own;
    setTarget(own);
    updateMeter(own);
    updateFaces(true); // faces follow finished estimates only, so they don't flicker
    if (state === 'player' && S.isSettled(board, own) && await confirmSettled(own) && state === 'player') finish('settled');
  }

  function playerMove(p) {
    if (state !== 'player') return;
    if (board.c[p] !== EMPTY) { poke(p); return; }
    if (p === board.ko) { nope(p); toast(t('ko')); return; }
    if (!board.isLegal(p)) { nope(p); toast(t('illegal')); return; }
    stopThinking();
    disarm();
    const captured = [];
    board.play(p, captured);
    capture(you, captured);
    sound.splat(1, 1);
    if (captured.length) setTimeout(() => sound.splat(0.7, 0.9), 90);
    buzz(captured.length ? [12, 60, 18] : 10);
    hideGhost();
    syncStones(board, p);
    afterMove();
  }

  function playerPass() {
    if (state !== 'player') return;
    stopThinking();
    board.play(PASS);
    toast(t('youPassed'));
    afterMove();
  }

  function afterMove() {
    if (board.passes >= 2 || board.moves >= MOVE_LIMIT) { finish('passes'); return; }
    if (board.turn === you) playerTurn();
    else cpuTurn();
  }

  async function cpuTurn() {
    state = 'cpu';
    setStatus(t('thinking'), 'cpu', true);
    $('pass').disabled = true;
    const lv = LEVELS[level];
    const gen = thinkGen;
    const started = performance.now();
    // Right after your pass the CPU also reads the board with you to move, so it passes
    // back once nothing is left to fill instead of throwing stones into your ground.
    const [s, o] = await Promise.all([think(board, lv.iters), board.passes > 0 ? think(flipped(board), CONFIRM_ITERS) : null]);
    const other = o && o.ownership();
    const d = S.decide(s, board, { temperature: lv.temperature, floor: lv.floor, shy: lv.shy, resign: lv.resign, other });
    await wait(CPU_MIN_MS - (performance.now() - started));
    if (gen !== thinkGen || state !== 'cpu') return;
    if (d.type === 'resign') { finish('cpu-resign'); return; }
    // よわい: opening on the centre point of a 5x5 board is too strong for a beginner.
    if (lv.offCenter && board.moves === 0 && d.type === 'move' && d.move === idx(N >> 1, N >> 1)) {
      const other = s.ranked().find((r) => r.move !== PASS && r.move !== d.move);
      if (other) d.move = other.move;
    }
    // Settled as the CPU sees it: the game ends here, rather than with a pass you would
    // have to answer.
    if (d.type === 'end') { finish('settled'); return; }
    cpuPlay(d.move);
  }

  function cpuPlay(move) {
    if (state !== 'cpu') return;
    if (move === PASS) {
      board.play(PASS);
      toast(t('cpuPassed'));
    } else {
      const before = yourAtari();
      const captured = [];
      board.play(move, captured);
      capture(3 - you, captured);
      sound.splat(0.85, 0.9);
      if (captured.length) { setTimeout(() => sound.splat(0.6, 0.9), 90); buzz([20, 50, 20]); }
      syncStones(board, move);
      ripple(move, COLORS.cpu);
      // A soft warning when this move put one of your groups in atari.
      if (!captured.length && [...yourAtari()].some((q) => !before.has(q))) setTimeout(() => sound.notes([392, 311], 0.09, 'triangle'), 260);
    }
    afterMove();
  }

  // Your stones whose group has a single liberty.
  function yourAtari() {
    const out = new Set();
    for (const p of POINTS) {
      if (board.c[p] !== you || out.has(p)) continue;
      const g = board.group(p);
      if (g.libs === 1) for (const q of g.stones) out.add(q);
    }
    return out;
  }

  // A ring that widens and fades where the CPU just played, so the eye finds it.
  function ripple(p, color) {
    const c = el('circle', { class: 'ripple', cx: px(p), cy: py(p), r: CELL * 0.46, fill: 'none', stroke: color, 'stroke-width': 7 }, fxLayer);
    setTimeout(() => c.remove(), 700);
  }

  // A red cross that shakes where you can't play.
  // A tap on a stone: it squishes a little (the point is taken).
  function poke(p) {
    const st = stoneEls.get(p);
    if (!st || st.g.classList.contains('drop')) return;
    st.g.classList.remove('poke');
    void st.g.getBBox();
    st.g.classList.add('poke');
    setTimeout(() => st.g.classList.remove('poke'), 360);
  }

  function nope(p) {
    const s = CELL * 0.17;
    const g = el('g', { class: 'nope', stroke: '#ff3b5c', 'stroke-width': 11, 'stroke-linecap': 'round' }, fxLayer);
    el('path', { d: `M${px(p) - s},${py(p) - s}L${px(p) + s},${py(p) + s}M${px(p) + s},${py(p) - s}L${px(p) - s},${py(p) + s}` }, g);
    setTimeout(() => g.remove(), 650);
    sound.notes([233, 175], 0.07, 'triangle');
    buzz([8, 40, 8]);
  }

  // The board only counts as finished if it is also settled with the other side to move
  // and both estimates agree on which stones are dead.
  function flipped(b) {
    const f = b.clone();
    f.turn = 3 - f.turn;
    f.ko = -1;
    f.passes = 0;
    return f;
  }
  async function confirmSettled(own) {
    const s = await think(flipped(board), CONFIRM_ITERS);
    return S.settledBoth(board, own, s.ownership());
  }

  async function finish(reason) {
    endReason = reason;
    settleFast = false;
    stopThinking();
    disarm();
    state = 'judging';
    $('pass').disabled = true;
    $('resign').disabled = true;
    hideGhost();
    hintLayer.textContent = '';
    if (reason === 'resign' || reason === 'cpu-resign') {
      const owner = new Int8Array(S.SIZE);
      for (const p of POINTS) owner[p] = target[p] > 0.3 ? 1 : target[p] < -0.3 ? -1 : 0;
      showResult({ win: reason === 'cpu-resign', reason: reason === 'resign' ? t('youResigned') : t('cpuResigned'), board: board.clone(), owner, dead: [], you });
      return;
    }
    sound.whistle();
    stamp(t('gameOver'));
    setStatus(t('counting'), '', true);
    if (reason === 'settled') toast(t('autoEnd'), 2800);
    $('game').classList.add('judging');
    const gen = gameGen;
    // Count on the estimate averaged over each side to move.
    const [s1, s2] = await Promise.all([think(board, FINAL_ITERS), think(flipped(board), FINAL_ITERS), wait(1250)]);
    if (gen !== gameGen) return; // a new game or the title took over meanwhile
    const j = S.judgeEnd(board, S.average(s1.ownership(), s2.ownership()));
    const finalBoard = board.clone();
    if (!await settle(j, gen) || gen !== gameGen) return;
    const owner = new Int8Array(S.SIZE);
    for (const p of POINTS) owner[p] = toMe(j.owner[p]);
    // Japanese counting: territory + prisoners (game + dead stones) + komi.
    const n = S.countJapanese(finalBoard, j);
    const cpuColor = 3 - you;
    const meKomi = you === WHITE ? KOMI : 0, cpuKomi = you === BLACK ? KOMI : 0;
    const r = {
      meTerr: n.terr[you], cpuTerr: n.terr[cpuColor], meAge: n.age[you], cpuAge: n.age[cpuColor], meKomi, cpuKomi,
      board: finalBoard, owner, dead: j.dead, seki: j.seki, you,
    };
    r.me = r.meTerr + r.meAge + meKomi;
    r.cpu = r.cpuTerr + r.cpuAge + cpuKomi;
    r.win = r.me > r.cpu;
    showResult(r);
  }

  // "Game over" stamped across the board for a moment (the count reads meanwhile).
  function stamp(text) {
    const el = $('stamp');
    el.textContent = text;
    el.style.fontSize = '';
    el.classList.remove('show');
    // A long word (other languages, small boards) shrinks to stay on the board.
    const room = el.parentNode.clientWidth * 0.86;
    if (el.offsetWidth > room) el.style.fontSize = `${parseFloat(getComputedStyle(el).fontSize) * room / el.offsetWidth}px`;
    void el.offsetWidth;
    el.classList.add('show');
  }

  // End-of-game cleanup on the board: show why the dead stones are dead and take them
  // off, show the eyes that keep groups alive, then fill each territory point with a
  // small counting stone while the meter counts up. Tapping the board hurries it along.
  // Resolves false if a new game or the title took over meanwhile.
  function settle(j, gen) {
    const T = (ms) => new Promise((r) => setTimeout(r, settleFast ? ms * 0.15 : ms)).then(() => { if (gen !== gameGen) throw new Error('stale'); });
    // The count starts from the prisoners taken during the game.
    const count = { black: prisoners[BLACK], white: prisoners[WHITE] };
    lastMark.setAttribute('cx', -100);
    hintLayer.textContent = '';
    return (async () => {
      // 1. Each dead chain goes grey and shows the one eye it has, if any. Pale stones of
      //    the other side then fill its liberties from outside, the eye last, and it is
      //    taken off: with fewer than two eyes it cannot escape that.
      const chains = deadChains(j.dead);
      if (chains.length) {
        setStatus(t('deadEyes'), '', false);
        for (const ch of chains) {
          for (const p of ch.stones) {
            const st = stoneEls.get(p);
            if (st) markDead(st.g, p);
          }
          ch.eyeMarks = ch.eyes.map((e) => makeEye(centerOf(e), false));
        }
        sound.notes([330, 277], 0.14, 'sine');
        await T(800);
        // All chains at once, one pale stone each per beat, every chain taken as its last
        // liberty fills: a couple of seconds however many there are.
        const take = (ch) => {
          for (const e of ch.eyeMarks) e.remove();
          // Taken: the stones fly to the capturer's tray, the capturer's ink floods in.
          for (const p of ch.stones) {
            const st = stoneEls.get(p);
            if (st) {
              st.g.classList.add('pop');
              const g = st.g;
              setTimeout(() => g.remove(), 340);
              stoneEls.delete(p);
            }
            splash(p, 3 - ch.color, 7, 0.9);
            // A dead stone is a prisoner for the other side.
            flyToTray(p, ch.color);
            if (ch.color === BLACK) count.white++;
            else count.black++;
          }
          updateMeter(null, count);
          sound.splat(0.7, 0.8);
        };
        const longest = Math.max(...chains.map((ch) => ch.libs.length));
        const step = Math.max(70, Math.min(180, 1500 / longest));
        const pale = new Map();
        for (let i = 0; i < longest; i++) {
          for (const ch of chains) {
            if (i >= ch.libs.length) continue;
            const q = ch.libs[i];
            if (!pale.has(q)) pale.set(q, makePale(q, 3 - ch.color));
            if (i === ch.libs.length - 1) take(ch);
          }
          sound.splat(1.5, 0.25);
          await T(step);
        }
        await T(380);
        for (const g of pale.values()) g.classList.add('fade');
        setTimeout(() => pale.forEach((g) => g.remove()), 400);
        await T(250);
      }
      // 2. Groups that live on two eyes show them.
      const after = board.clone();
      for (const p of j.dead) after.c[p] = EMPTY;
      const alive = twoEyed(after);
      const beaming = new Set();
      for (const g of alive) for (const q of g.stones) beaming.add(q);
      for (const [q, st] of stoneEls) setFace(st, q, beaming.has(q) ? 4 : 0);
      if (alive.length) {
        setStatus(t('aliveEyes'), '', false);
        const marks = [];
        // Every eye gets its mark, big pieces of ground too (each counts as an eye).
        const marked = new Set();
        for (const g of S.groupsOf(after)) for (const e of g.eyes) {
          const key = e.join();
          if (marked.has(key)) continue;
          marked.add(key);
          marks.push(makeEye(centerOf(e), true));
        }
        sound.notes([523, 784], 0.12, 'triangle');
        await T(2000);
        for (const m of marks) m.classList.add('fade');
        setTimeout(() => marks.forEach((m) => m.remove()), 400);
      }
      // 3. Seki: neither side can fill the shared points, so both live and those points
      //    (and the eyes of groups in seki) belong to nobody.
      const sekiPoints = sekiLiberties(after, j.seki);
      if (sekiPoints.size) {
        setStatus(t('sekiNote'), '', false);
        for (const p of sekiPoints) markSeki(p);
        sound.notes([440, 440], 0.12, 'triangle');
        await T(2200);
      }
      setStatus(t('counting'), '', true);
      // 4. The ink dries into a clear map: one tile per point, colored by its owner.
      for (const p of POINTS) {
        const v = board.c[p];
        if (v !== EMPTY && !j.dead.includes(p)) {
          target[p] = v === you ? 1 : -1;
          paintTile(p, v);
        } else if (j.owner[p] === 0) {
          target[p] = 0;
          paintTile(p, EMPTY);
          if (!sekiPoints.has(p)) markDame(p);
        }
      }
      inkDry = true;
      inkLayers.me.classList.add('dry');
      inkLayers.cpu.classList.add('dry');
      const layers = [inkLayers.me, inkLayers.cpu];
      setTimeout(() => layers.forEach((l) => { l.style.display = 'none'; }), 650);
      updateMeter(null, count);
      await T(450);
      // 5. Count the territory (empty points) with a counting stone each: yours first.
      const spots = [];
      for (const side of [toMe(1), toMe(-1)]) {
        for (const p of POINTS) {
          const empty = board.c[p] === EMPTY || j.dead.includes(p);
          if (empty && j.owner[p] === side) spots.push(p);
        }
      }
      const step = spots.length ? Math.min(80, 1400 / spots.length) : 0;
      let i = 0;
      for (const p of spots) {
        const side = j.owner[p] > 0 ? BLACK : WHITE;
        makeDummy(p, side);
        paintTile(p, side);
        if (side === BLACK) count.black++;
        else count.white++;
        updateMeter(null, count);
        sound.splat(1.3 + (i++ % 12) * 0.05, 0.3);
        await T(step);
      }
      await T(700);
      return true;
    })().catch(() => false);
  }

  let settleFast = false;

  function markDead(g, p) {
    g.classList.remove('drop');
    g.classList.add('dying');
    el('circle', { cx: px(p), cy: py(p), r: CELL * 0.43, fill: '#8f8aa3', class: 'dead-cover' }, g);
    const st = stoneEls.get(p);
    if (st) { st.mood = -1; setFace(st, p, 3); }
  }

  // Dead stones by chain: [{color, stones, eyes, libs}], libs in the order the other
  // side would fill them: around the outside first, then the eye, its last point taking
  // the chain.
  function deadChains(dead) {
    const groups = S.groupsOf(board);
    const out = [];
    const seen = new Set();
    for (const p of dead) {
      if (seen.has(p)) continue;
      const g = groups.find((x) => x.stones.includes(p));
      for (const q of g.stones) seen.add(q);
      const inEye = new Set(g.eyes.flat());
      const outside = new Set();
      for (const q of g.stones) for (const d of [1, -1, S.W, -S.W]) if (board.c[q + d] === EMPTY && !inEye.has(q + d)) outside.add(q + d);
      // Sweep around the chain.
      let cx = 0, cy = 0;
      for (const q of g.stones) { cx += xOf(q); cy += yOf(q); }
      cx /= g.stones.length; cy /= g.stones.length;
      const angle = (q) => Math.atan2(yOf(q) - cy, xOf(q) - cx);
      const around = [...outside].sort((a, b) => angle(a) - angle(b));
      // Inside the eye the point with the most room goes first.
      const room = (q) => [1, -1, S.W, -S.W].filter((d) => inEye.has(q + d)).length;
      const eye = [...inEye].sort((a, b) => room(b) - room(a));
      out.push({ color: g.color, stones: g.stones, eyes: g.eyes, libs: around.concat(eye) });
    }
    return out;
  }

  // The point of an area with the most neighbours inside it.
  function centerOf(points) {
    const set = new Set(points);
    let best = points[0], most = -1;
    for (const q of points) {
      const n = [1, -1, S.W, -S.W].filter((d) => set.has(q + d)).length;
      if (n > most) { most = n; best = q; }
    }
    return best;
  }

  // An eye drawn on an empty point. alive: one of two eyes that keep a group alive;
  // otherwise the lone eye of a dead chain.
  function makeEye(p, alive) {
    const g = el('g', { class: 'eye-mark ' + (alive ? 'alive' : 'lone') }, hintLayer);
    const cx = px(p), cy = py(p), w = CELL * 0.3, h = CELL * 0.19;
    el('path', { d: `M${cx - w},${cy}Q${cx},${cy - h * 1.9} ${cx + w},${cy}Q${cx},${cy + h * 1.9} ${cx - w},${cy}Z`, fill: '#fff', stroke: '#120b28', 'stroke-width': 6, 'stroke-linejoin': 'round' }, g);
    el('circle', { cx, cy, r: h * 0.78, fill: alive ? '#120b28' : '#5d5875' }, g);
    el('circle', { cx: cx - h * 0.28, cy: cy - h * 0.3, r: h * 0.24, fill: '#fff' }, g);
    return g;
  }

  // A see-through stone: where the other side could play to take a dead chain.
  function makePale(p, color) {
    const side = sideOf(color);
    const g = el('g', { class: 'stone pale drop' }, stoneLayer);
    el('circle', { cx: px(p), cy: py(p), r: CELL * 0.4, fill: COLORS[side + 'Light'], 'fill-opacity': 0.8, stroke: '#120b28', 'stroke-width': 6, 'stroke-dasharray': '12 9' }, g);
    return g;
  }

  // Empty points shared by groups in seki (not their eyes): labelled セキ at the end.
  function sekiLiberties(b, seki) {
    const set = new Set(seki);
    const out = new Set();
    for (const p of POINTS) {
      if (b.c[p] !== EMPTY) continue;
      let colors = 0;
      for (const d of [1, -1, S.W, -S.W]) if (set.has(p + d)) colors |= b.c[p + d];
      if (colors === 3) out.add(p);
    }
    return out;
  }

  function markSeki(p) {
    const g = el('g', { class: 'seki-mark' }, stoneLayer);
    const w = CELL * 0.84, h = CELL * 0.42;
    el('rect', { x: px(p) - w / 2, y: py(p) - h / 2, width: w, height: h, rx: h / 2, fill: '#120b28', stroke: '#fff', 'stroke-width': 4 }, g);
    const text = el('text', { x: px(p), y: py(p), 'text-anchor': 'middle', 'dominant-baseline': 'central', fill: '#fff', 'font-size': CELL * 0.25, 'font-family': cssVar('--font-head') || 'sans-serif' }, g);
    text.textContent = t('seki');
  }

  // Territory marker: a flat, pale disc (living stones stay glossy and bigger).
  function makeDummy(p, color) {
    const side = sideOf(color);
    const g = el('g', { class: 'stone dummy drop' }, stoneLayer);
    el('circle', { cx: px(p), cy: py(p), r: CELL * 0.26, fill: COLORS[side + 'Light'], stroke: '#120b28', 'stroke-width': 5 }, g);
    return g;
  }

  function paintTile(p, color) {
    if (color === EMPTY) return;
    finalOwner[p] = color === you ? 1 : -1;
    const layer = color === you ? tileLayer.me : tileLayer.cpu;
    for (const [x, y, r] of puddleCircles(p, finalOwner)) {
      el('circle', { cx: MARGIN + x * CELL, cy: MARGIN + y * CELL, r: r * CELL }, layer);
    }
  }

  function markDame(p) {
    const s = CELL * 0.13;
    el('path', {
      d: `M${px(p) - s},${py(p) - s}L${px(p) + s},${py(p) + s}M${px(p) + s},${py(p) - s}L${px(p) - s},${py(p) + s}`,
      stroke: '#7d7891', 'stroke-width': 8, 'stroke-linecap': 'round', fill: 'none', class: 'dame-mark',
    }, stoneLayer);
  }

  function showResult(r) {
    state = 'over';
    lastResult = r;
    shareBlob = null;
    shareImage = new Promise((res) => setTimeout(res, 1600)).then(() => (lastResult === r ? renderShareImage(r) : null)).catch(() => null);
    shareImage.then((b) => { if (lastResult === r) shareBlob = b; });
    const sp = $('result-splat');
    sp.textContent = '';
    const color = r.win ? COLORS.me : COLORS.cpu;
    const other = r.win ? COLORS.cpu : COLORS.me;
    const seed = (Math.random() * 1e9) | 0;
    splatGroup(sp, 330, 40, 90, color, seed + 1, 0);
    splatGroup(sp, 40, 120, 60, other, seed + 2, 0.08);
    splatGroup(sp, 60, 380, 90, color, seed + 3, 0.12);
    $('result-word').textContent = r.win ? 'WIN!' : 'LOSE...';
    $('result-word').className = 'result-word ' + (r.win ? 'win' : 'lose');
    $('result-reason').textContent = r.reason || '';
    $('result-bars').hidden = r.me == null;
    $('tally').hidden = r.me == null;
    if (r.me != null) {
      const segs = {
        me: r.meTerr, 'me-age': r.meAge, 'me-komi': r.meKomi,
        'cpu-komi': r.cpuKomi, 'cpu-age': r.cpuAge, cpu: r.cpuTerr,
      };
      const total = Object.values(segs).reduce((a, v) => a + v, 0) || 1;
      let before = 0;
      tallyCaptions = [];
      for (const k in segs) {
        $('tl-' + k).style.flexGrow = 0;
        const cap = $('tc-' + k);
        cap.textContent = '';
        if (k.endsWith('komi') && segs[k]) {
          cap.textContent = `${t('komi')} ${segs[k]}`;
          tallyCaptions.push({ el: cap, at: (before + segs[k] / 2) / total });
        }
        before += segs[k];
      }
      // Grow the bar after it is on screen.
      setTimeout(() => { for (const k in segs) $('tl-' + k).style.flexGrow = segs[k]; }, 250);
      $('res-me').textContent = r.me;
      $('res-cpu').textContent = r.cpu;
      $('res-me-note').textContent = breakdown(r.meTerr, r.meAge, r.meKomi);
      $('res-cpu-note').textContent = breakdown(r.cpuTerr, r.cpuAge, r.cpuKomi);
    }
    // A first win at this level, or a run of wins, gets a word under the result.
    const rec = addRecord(r.win);
    const cheer = !r.win ? '' : rec.w === 1 ? t('firstWin') : rec.s >= 2 ? t('streak', { n: rec.s }) : '';
    $('result-reason').textContent = [r.reason, cheer].filter(Boolean).join(' · ');
    // The winner's stones hop in a wave, the loser's look worried.
    const winner = r.win ? you : 3 - you;
    for (const [q, st] of stoneEls) {
      if (st.color === winner) {
        setFace(st, q, 4);
        st.g.style.setProperty('--d', ((xOf(q) + yOf(q)) * 55 + 300) + 'ms');
        st.g.classList.add('cheer');
      } else setFace(st, q, 1);
    }
    // After a win, an offer to go one level up.
    const next = r.win && NEXT_LEVEL[level];
    $('next-level').hidden = !next;
    if (next) $('next-level').textContent = t('nextLevel', { lv: t(next) });
    $('game').classList.remove('judging');
    $('game').classList.add('over');
    placeCaptions();
    if (r.win) sound.win();
    else sound.lose();
  }

  // Komi labels sit under their stripes but stay inside the bar's width (a small komi
  // at the far end would otherwise hang off the edge).
  let tallyCaptions = [];
  function placeCaptions() {
    const width = $('tally').clientWidth;
    for (const c of tallyCaptions) {
      const w = c.el.offsetWidth;
      c.el.style.left = Math.max(0, Math.min(width - w, c.at * width - w / 2)) + 'px';
    }
  }
  window.addEventListener('resize', () => { if (state === 'over') placeCaptions(); });

  // "地 8 + アゲハマ 3 + コミ 4.5"
  function breakdown(terr, age, komi) {
    // No-break spaces keep each term on one line when the note wraps.
    let s = `${t('territory')} ${terr} + ${t('prisoners')} ${age}`;
    if (komi) s += ` + ${t('komi')} ${komi}`;
    return s;
  }

  function shareText() {
    const r = lastResult;
    const vars = { lv: t(level), me: r && r.me, cpu: r && r.cpu };
    let key;
    if (!r) return 'stoon';
    if (r.me != null) key = r.win ? 'shareWin' : 'shareLose';
    else key = r.win ? 'shareWinResign' : 'shareLoseResign';
    const rec = loadRecord()[level];
    const streak = r.win && rec && rec.s >= 2 ? ' ' + t('streak', { n: rec.s }) : '';
    return t(key, vars) + streak + ' #stoon';
  }

  // ---------- share card ----------

  let shareImage = null; // Promise<Blob|null> for the last result
  let shareBlob = null;

  function cssVar(name) {
    return getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  }

  async function fontsReady(fonts) {
    if (!document.fonts || !document.fonts.load) return;
    const wait = Promise.all(fonts.map((f) => document.fonts.load(f).catch(() => null)));
    await Promise.race([wait, new Promise((r) => setTimeout(r, 1500))]);
  }

  function roundRect(ctx, x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  function drawStone(ctx, x, y, r, side, alpha) {
    const c = side === 'me'
      ? [COLORS.meLight, COLORS.me, COLORS.meDeep]
      : [COLORS.cpuLight, COLORS.cpu, COLORS.cpuDeep];
    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.fillStyle = 'rgba(18,11,40,0.45)';
    ctx.beginPath(); ctx.arc(x, y + r * 0.16, r, 0, Math.PI * 2); ctx.fill();
    const g = ctx.createRadialGradient(x - r * 0.3, y - r * 0.35, r * 0.05, x, y, r * 1.1);
    g.addColorStop(0, c[0]); g.addColorStop(0.6, c[1]); g.addColorStop(1, c[2]);
    ctx.fillStyle = g;
    ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fill();
    ctx.lineWidth = r * 0.12;
    ctx.strokeStyle = '#120b28';
    ctx.stroke();
    ctx.fillStyle = 'rgba(255,255,255,0.85)';
    ctx.beginPath(); ctx.ellipse(x - r * 0.3, y - r * 0.37, r * 0.25, r * 0.16, -0.6, 0, Math.PI * 2); ctx.fill();
    ctx.restore();
  }

  function drawSmile(ctx, x, y, r, ink) {
    ctx.save();
    ctx.fillStyle = ink;
    ctx.strokeStyle = ink;
    ctx.lineWidth = r * 0.09;
    ctx.lineCap = 'round';
    ctx.fillStyle = 'rgba(255,143,179,0.6)';
    for (const s of [-1, 1]) { ctx.beginPath(); ctx.ellipse(x + s * 0.46 * r, y + 0.12 * r, 0.13 * r, 0.075 * r, 0, 0, Math.PI * 2); ctx.fill(); }
    for (const s of [-1, 1]) {
      ctx.fillStyle = '#120b28';
      ctx.beginPath(); ctx.ellipse(x + s * 0.3 * r, y - 0.06 * r, 0.085 * r, 0.12 * r, 0, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = '#fff';
      ctx.beginPath(); ctx.arc(x + (s * 0.3 - 0.03) * r, y - 0.11 * r, 0.035 * r, 0, Math.PI * 2); ctx.fill();
    }
    ctx.beginPath(); ctx.moveTo(x - 0.13 * r, y + 0.2 * r); ctx.quadraticCurveTo(x, y + 0.33 * r, x + 0.13 * r, y + 0.2 * r); ctx.stroke();
    ctx.restore();
  }

  function outlinedText(ctx, text, x, y, stroke) {
    ctx.lineJoin = 'round';
    ctx.lineWidth = stroke;
    ctx.strokeStyle = '#120b28';
    ctx.fillStyle = '#120b28';
    ctx.fillText(text, x + stroke * 0.4, y + stroke * 0.7);
    ctx.strokeText(text, x + stroke * 0.4, y + stroke * 0.7);
    ctx.strokeText(text, x, y);
    ctx.fillStyle = '#fff';
    ctx.fillText(text, x, y);
  }

  // 1200x675 image of the final board and the score.
  async function renderShareImage(r) {
    const logoFont = '"Bowlby One", sans-serif';
    const headFont = cssVar('--font-head') || 'sans-serif';
    await fontsReady([`120px ${logoFont}`, `40px ${headFont}`]);
    const W = 1200, H = 675;
    const cv = document.createElement('canvas');
    cv.width = W; cv.height = H;
    const ctx = cv.getContext('2d');

    ctx.fillStyle = '#1b1236';
    ctx.fillRect(0, 0, W, H);
    ctx.save();
    ctx.strokeStyle = 'rgba(255,255,255,0.03)';
    ctx.lineWidth = 22;
    for (let x = -H; x < W; x += 44) { ctx.beginPath(); ctx.moveTo(x, H); ctx.lineTo(x + H, 0); ctx.stroke(); }
    ctx.restore();
    const win = r.win;
    ctx.fillStyle = win ? COLORS.me : COLORS.cpu;
    ctx.fill(new Path2D(splatPath(930, 250, 190, 978)));
    ctx.fillStyle = win ? COLORS.cpu : COLORS.me;
    ctx.fill(new Path2D(splatPath(1160, 640, 110, 979)));

    // Board
    const B = 595, bx = 40, by = 40, m = N <= 5 ? 64 : 52, cell = (B - 2 * m) / (N - 1);
    const X = (p) => bx + m + xOf(p) * cell, Y = (p) => by + m + yOf(p) * cell;
    ctx.fillStyle = 'rgba(12,7,32,0.55)';
    roundRect(ctx, bx, by + 8, B, B, 32); ctx.fill();
    ctx.fillStyle = '#e9e5f0';
    roundRect(ctx, bx, by, B, B, 32); ctx.fill();
    ctx.save();
    roundRect(ctx, bx, by, B, B, 32); ctx.clip();
    const b = r.board;
    const dead = new Set(r.dead);
    const counted = r.me != null;
    for (const p of POINTS) {
      const o = r.owner[p];
      if (!o) continue;
      ctx.fillStyle = o > 0 ? COLORS.me : COLORS.cpu;
      ctx.beginPath();
      for (const [x, y, rr] of puddleCircles(p, r.owner)) {
        const cx = bx + m + x * cell, cy = by + m + y * cell;
        ctx.moveTo(cx + rr * cell, cy);
        ctx.arc(cx, cy, rr * cell, 0, Math.PI * 2);
      }
      ctx.fill();
    }
    ctx.restore();
    ctx.strokeStyle = 'rgba(42,31,77,0.38)';
    ctx.lineWidth = 3;
    ctx.lineCap = 'round';
    for (let i = 0; i < N; i++) {
      const v = m + i * cell;
      ctx.beginPath(); ctx.moveTo(bx + m, by + v); ctx.lineTo(bx + B - m, by + v); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(bx + v, by + m); ctx.lineTo(bx + v, by + B - m); ctx.stroke();
    }
    for (const p of POINTS) {
      const v = b.c[p];
      if (v !== EMPTY && !dead.has(p)) {
        drawStone(ctx, X(p), Y(p), cell * 0.43, v === r.you ? 'me' : 'cpu', 1);
        drawSmile(ctx, X(p), Y(p), cell * 0.43, v === r.you ? COLORS.meOn : COLORS.cpuOn);
      } else if (counted && r.owner[p] !== 0) {
        ctx.fillStyle = r.owner[p] > 0 ? COLORS.meLight : COLORS.cpuLight;
        ctx.strokeStyle = '#120b28';
        ctx.lineWidth = 4;
        ctx.beginPath(); ctx.arc(X(p), Y(p), cell * 0.26, 0, Math.PI * 2); ctx.fill(); ctx.stroke();
      } else if (counted) {
        const s = cell * 0.13;
        ctx.strokeStyle = '#7d7891';
        ctx.lineWidth = 6;
        ctx.lineCap = 'round';
        ctx.beginPath(); ctx.moveTo(X(p) - s, Y(p) - s); ctx.lineTo(X(p) + s, Y(p) + s);
        ctx.moveTo(X(p) + s, Y(p) - s); ctx.lineTo(X(p) - s, Y(p) + s); ctx.stroke();
      }
    }

    // Logo: "st" + two stones + "n"
    ctx.textBaseline = 'alphabetic';
    ctx.textAlign = 'left';
    ctx.font = `92px ${logoFont}`;
    const wSt = ctx.measureText('st').width, wN = ctx.measureText('n').width;
    const sr = 30, gap = 4;
    let lx = 930 - (wSt + wN + sr * 4 + gap * 3) / 2;
    const ly = 150;
    outlinedText(ctx, 'st', lx, ly, 14);
    lx += wSt + gap;
    drawStone(ctx, lx + sr, ly - 30, sr, 'me', 1);
    lx += sr * 2 + gap;
    drawStone(ctx, lx + sr, ly - 34, sr, 'cpu', 1);
    lx += sr * 2 + gap;
    outlinedText(ctx, 'n', lx, ly, 14);

    // Result word
    ctx.save();
    ctx.translate(930, 262);
    ctx.rotate(-0.08);
    ctx.textAlign = 'center';
    ctx.font = `${win ? 118 : 96}px ${logoFont}`;
    outlinedText(ctx, win ? 'WIN!' : 'LOSE...', 0, 40, 16);
    ctx.restore();

    // Tally: board points and striped komi on one bar; the middle line decides.
    let ry = 400;
    if (r.me != null) {
      const tx = 720, tw = 420, ty = 340, th = 30;
      const segs = [
        [r.meTerr, COLORS.me, ''], [r.meAge, COLORS.me, 'dots'], [r.meKomi, COLORS.me, 'stripes'],
        [r.cpuKomi, COLORS.cpu, 'stripes'], [r.cpuAge, COLORS.cpu, 'dots'], [r.cpuTerr, COLORS.cpu, ''],
      ];
      const total = segs.reduce((a, s) => a + s[0], 0);
      ctx.fillStyle = '#120b28';
      roundRect(ctx, tx - 6, ty - 6, tw + 12, th + 12, (th + 12) / 2); ctx.fill();
      const captions = [];
      ctx.save();
      roundRect(ctx, tx, ty, tw, th, th / 2); ctx.clip();
      let sx = tx;
      for (const [v, col, pattern] of segs) {
        const w = (v / total) * tw;
        if (w <= 0) continue;
        ctx.fillStyle = col;
        ctx.fillRect(sx, ty, w + 0.5, th);
        if (pattern === 'dots') {
          ctx.save();
          ctx.beginPath(); ctx.rect(sx, ty, w, th); ctx.clip();
          ctx.fillStyle = 'rgba(255,255,255,0.6)';
          for (let dx = 6; dx < w + 6; dx += 12) {
            for (const dy of [8, 22]) { ctx.beginPath(); ctx.arc(sx + dx + (dy === 22 ? 6 : 0), ty + dy, 3.2, 0, Math.PI * 2); ctx.fill(); }
          }
          ctx.restore();
        }
        if (pattern === 'stripes') {
          ctx.save();
          ctx.beginPath(); ctx.rect(sx, ty, w, th); ctx.clip();
          ctx.strokeStyle = 'rgba(255,255,255,0.55)';
          ctx.lineWidth = 6;
          for (let k = -th; k < w + th; k += 14) { ctx.beginPath(); ctx.moveTo(sx + k, ty + th); ctx.lineTo(sx + k + th, ty); ctx.stroke(); }
          ctx.restore();
          captions.push([`${t('komi')} ${v}`, sx + w / 2]);
        }
        sx += w;
      }
      ctx.restore();
      ctx.fillStyle = '#fff';
      ctx.fillRect(tx + tw / 2 - 2.5, ty - 8, 5, th + 16);
      ctx.font = `20px ${headFont}`;
      ctx.textAlign = 'center';
      for (const [text, cx] of captions) {
        const w = ctx.measureText(text).width + 20;
        ctx.fillStyle = '#120b28';
        roundRect(ctx, cx - w / 2, ty + th + 8, w, 30, 8); ctx.fill();
        ctx.fillStyle = '#fff';
        ctx.fillText(text, cx, ty + th + 30);
      }
      ry = 418;
    }
    // Score rows, or the reason for a resignation
    if (r.me != null) {
      for (const [side, label, value, color, sub] of [
        ['me', t('you'), r.me, COLORS.meText, breakdown(r.meTerr, r.meAge, r.meKomi)],
        ['cpu', t('cpu'), r.cpu, COLORS.cpuText, breakdown(r.cpuTerr, r.cpuAge, r.cpuKomi)],
      ]) {
        ctx.fillStyle = '#120b28';
        roundRect(ctx, 720, ry, 420, 74, 18); ctx.fill();
        ctx.fillStyle = side === 'me' ? COLORS.me : COLORS.cpu;
        ctx.beginPath(); ctx.arc(752, ry + 37, 11, 0, Math.PI * 2); ctx.fill();
        ctx.textAlign = 'left';
        ctx.fillStyle = '#fff';
        ctx.font = `30px ${headFont}`;
        ctx.fillText(label, 776, sub ? ry + 36 : ry + 48);
        ctx.textAlign = 'right';
        ctx.fillStyle = color;
        ctx.font = `46px ${headFont}`;
        ctx.fillText(String(value), 1116, ry + 55);
        if (sub) {
          // The breakdown keeps clear of the total: smaller type when it runs long.
          const room = 1116 - ctx.measureText(String(value)).width - 18 - 776;
          ctx.textAlign = 'left';
          let size = 19;
          ctx.font = `${size}px ${headFont}`;
          while (size > 13 && ctx.measureText(sub).width > room) ctx.font = `${--size}px ${headFont}`;
          ctx.fillStyle = '#b9b0d6';
          ctx.fillText(sub, 776, ry + 62, room); // still too long: squeezed to fit
        }
        ry += 88;
      }
    } else if (r.reason) {
      ctx.font = `34px ${headFont}`;
      const w = ctx.measureText(r.reason).width + 48;
      ctx.fillStyle = '#120b28';
      roundRect(ctx, 930 - w / 2, 420, w, 64, 12); ctx.fill();
      ctx.fillStyle = '#fff';
      ctx.textAlign = 'center';
      ctx.fillText(r.reason, 930, 464);
      ry = 520;
    }
    ctx.fillStyle = '#b9b0d6';
    ctx.font = `26px ${headFont}`;
    ctx.textAlign = 'center';
    const rec = loadRecord()[level];
    const streak = r.win && rec && rec.s >= 2 ? ' · ' + t('streak', { n: rec.s }) : '';
    ctx.fillText(t('cardLevel', { lv: t(level) }) + streak, 930, Math.min(ry + 36, 650));

    return new Promise((res) => cv.toBlob((bl) => res(bl), 'image/png'));
  }

  function download(blob) {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'stoon.png';
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 4000);
  }

  // Phones: share sheet with the image (pick X there). Elsewhere: copy the image,
  // open X's composer with the text, and let the player paste it.
  function share() {
    // The link opens the game at the level just played.
    const url = location.origin + location.pathname + '?level=' + level;
    const text = shareText();
    const blob = shareBlob;
    const coarse = window.matchMedia && matchMedia('(pointer: coarse)').matches;
    if (blob && coarse && navigator.canShare) {
      const file = new File([blob], 'stoon.png', { type: 'image/png' });
      const data = { files: [file], text: text + ' ' + url };
      if (navigator.canShare(data)) {
        navigator.share(data).catch((e) => { if (e && e.name !== 'AbortError') openIntent(text, url, blob); });
        return;
      }
    }
    openIntent(text, url, blob);
  }

  function openIntent(text, url, blob) {
    // Inside a frame (the X card), copying and saving are blocked: the post carries the
    // link, and its card shows the picture.
    let framed = true;
    try { framed = window.top !== window.self; } catch (e) { /* cross-origin: framed */ }
    if (blob && !framed) {
      let copying = null;
      try {
        if (navigator.clipboard && window.ClipboardItem) copying = navigator.clipboard.write([new ClipboardItem({ 'image/png': blob })]);
      } catch (e) { copying = null; }
      (copying || Promise.reject(new Error('no clipboard')))
        .then(() => toast(t('copied')))
        .catch(() => { download(blob); toast(t('saved')); });
    }
    const intent = 'https://x.com/intent/post?text=' + encodeURIComponent(text) + '&url=' + encodeURIComponent(url);
    window.open(intent, '_blank', 'noopener');
  }

  // Two-tap confirm for buttons that lose the game. Armed long enough to read the warning.
  const ARM_MS = 4200;
  let armed = null, armedHtml = '', armTimer = 0;
  function arm(btn, label, action) {
    if (armed === btn) { disarm(); action(); return; }
    disarm();
    armed = btn;
    armedHtml = btn.innerHTML;
    if (label) btn.textContent = label;
    btn.classList.add('armed');
    armTimer = setTimeout(disarm, ARM_MS);
  }
  function disarm() {
    clearTimeout(armTimer);
    if (toastHeld) hideToast();
    if (armed) {
      armed.innerHTML = armedHtml;
      armed.classList.remove('armed');
    }
    armed = null;
  }

  // Wins and losses per level, kept on this device.
  function loadRecord() {
    try { return JSON.parse(store.get('record', '{}')) || {}; } catch (e) { return {}; }
  }
  // Returns the level's record after this game: {w, l, s (wins in a row)}.
  function addRecord(win) {
    const rec = loadRecord();
    const r = rec[level] || { w: 0, l: 0, s: 0 };
    if (win) { r.w++; r.s = (r.s || 0) + 1; } else { r.l++; r.s = 0; }
    rec[level] = r;
    store.set('record', JSON.stringify(rec));
    return r;
  }

  const NEXT_LEVEL = { easy: 'normal', normal: 'strong' };

  // A screen slides in when it is shown.
  function enter(screen) {
    screen.classList.remove('enter');
    void screen.offsetWidth;
    screen.classList.add('enter');
  }

  function toTitle() {
    stopThinking();
    gameGen++;
    disarm();
    syncLevel();
    state = 'idle';
    $('game').hidden = true;
    $('game').classList.remove('over');
    $('title').hidden = false;
    enter($('title'));
    pickInks();
    drawTitle();
  }

  // ---------- input ----------

  function pointAt(evt) {
    const pt = boardSvg.createSVGPoint();
    pt.x = evt.clientX;
    pt.y = evt.clientY;
    const m = boardSvg.getScreenCTM();
    if (!m) return -1;
    const q = pt.matrixTransform(m.inverse());
    const x = Math.round((q.x - MARGIN) / CELL);
    const y = Math.round((q.y - MARGIN) / CELL);
    if (x < 0 || y < 0 || x >= N || y >= N) return -1;
    const dx = q.x - (MARGIN + x * CELL), dy = q.y - (MARGIN + y * CELL);
    if (dx * dx + dy * dy > CELL * CELL * 0.36) return -1;
    return idx(x, y);
  }

  function hideGhost() { ghost.setAttribute('cx', -100); }

  boardSvg.addEventListener('pointermove', (e) => {
    if (e.pointerType !== 'mouse' || state !== 'player') return;
    const p = pointAt(e);
    if (p >= 0 && board.c[p] === EMPTY && p !== board.ko && board.isLegal(p)) {
      ghost.setAttribute('cx', px(p));
      ghost.setAttribute('cy', py(p));
    } else hideGhost();
  });
  boardSvg.addEventListener('pointerleave', hideGhost);

  // Keyboard: arrows move the see-through stone, Enter or Space plays there.
  let cursor = -1;
  boardSvg.setAttribute('tabindex', '0');
  boardSvg.addEventListener('keydown', (e) => {
    const step = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1] }[e.key];
    if (!step && e.key !== 'Enter' && e.key !== ' ') return;
    e.preventDefault();
    if (state !== 'player') return;
    if (!POINTS.includes(cursor)) cursor = idx(N >> 1, N >> 1);
    else if (step) {
      const x = Math.max(0, Math.min(N - 1, xOf(cursor) + step[0]));
      const y = Math.max(0, Math.min(N - 1, yOf(cursor) + step[1]));
      cursor = idx(x, y);
    } else {
      playerMove(cursor);
      return;
    }
    ghost.setAttribute('cx', px(cursor));
    ghost.setAttribute('cy', py(cursor));
  });
  boardSvg.addEventListener('blur', hideGhost);
  boardSvg.addEventListener('pointerup', (e) => {
    sound.ensure(); // a phone call or a trip to another app can suspend the sound
    if (state === 'judging') { settleFast = true; return; }
    const p = pointAt(e);
    if (p >= 0) playerMove(p);
  });

  $('start').addEventListener('click', () => startGame());
  $('again').addEventListener('click', () => { pickInks(); startGame(); });
  $('to-title').addEventListener('click', toTitle);
  $('next-level').addEventListener('click', () => {
    if (!NEXT_LEVEL[level]) return;
    level = NEXT_LEVEL[level];
    store.set('level', level);
    syncLevel();
    pickInks();
    startGame();
  });
  $('share').addEventListener('click', share);
  $('pass').addEventListener('click', (e) => {
    if (state !== 'player') return;
    // While the board is still open a pass can end the game (the CPU may pass back), so
    // it takes a second tap.
    if (yourOwn && S.isSettled(board, yourOwn)) { disarm(); playerPass(); return; }
    const first = armed !== e.currentTarget;
    arm(e.currentTarget, t('passConfirm'), playerPass);
    if (first) toast(t('passWarn'), ARM_MS, true);
  });
  $('resign').addEventListener('click', (e) => arm(e.currentTarget, t('resignConfirm'), () => { if (state === 'player' || state === 'cpu') finish('resign'); }));
  $('back').addEventListener('click', (e) => {
    if (state === 'over' || state === 'idle') { toTitle(); return; }
    const first = armed !== e.currentTarget;
    arm(e.currentTarget, '', toTitle);
    if (first) toast(t('backConfirm'), ARM_MS, true);
  });
  // ---------- how to play: a small picture beside each line ----------
  // Drawn once in the page's ink colors (CSS variables, so they follow every new pair).
  // A small stone as SVG markup in the page's ink colors (CSS variables). face: smile,
  // beam, dead, think.
  function stoneSvg(x, y, r, side, face = 'smile') {
    const NAVY = '#120b28';
    const f = (v) => +v.toFixed(1);
    const fill = side === 'grey' ? '#8f8aa3' : `var(--${side})`;
    const ink = side === 'grey' ? NAVY : `var(--${side}-on)`;
    const P = (dx, dy) => `${f(x + dx * r)},${f(y + dy * r)}`;
    let s = `<circle cx="${x}" cy="${y}" r="${r}" style="fill:${fill}" stroke="${NAVY}" stroke-width="${f(r * 0.16)}"/>`;
    if (side !== 'grey') s += `<ellipse cx="${f(x - r * 0.45)}" cy="${f(y - r * 0.5)}" rx="${f(r * 0.2)}" ry="${f(r * 0.12)}" fill="#fff" opacity="0.8" transform="rotate(-35 ${f(x - r * 0.45)} ${f(y - r * 0.5)})"/>`;
    const line = `fill="none" style="stroke:${ink}" stroke-width="${f(r * 0.13)}" stroke-linecap="round"`;
    const dot = (dx, dy) => `<circle cx="${f(x + dx * r)}" cy="${f(y + dy * r)}" r="${f(r * 0.1)}" style="fill:${ink}"/>`;
    if (face === 'smile') {
      s += dot(-0.3, -0.06) + dot(0.3, -0.06) + `<path d="M${P(-0.15, 0.2)}Q${P(0, 0.34)} ${P(0.15, 0.2)}" ${line}/>`;
    } else if (face === 'think') {
      s += dot(-0.18, -0.2) + dot(0.38, -0.2) + `<circle cx="${f(x + r * 0.12)}" cy="${f(y + r * 0.28)}" r="${f(r * 0.09)}" ${line}/>`;
    } else if (face === 'beam') {
      s += `<path d="M${P(-0.42, 0)}Q${P(-0.3, -0.22)} ${P(-0.18, 0)}M${P(0.18, 0)}Q${P(0.3, -0.22)} ${P(0.42, 0)}M${P(-0.16, 0.17)}Q${P(0, 0.36)} ${P(0.16, 0.17)}" ${line}/>`;
    } else if (face === 'dead') {
      s += `<path d="M${P(-0.42, -0.2)}L${P(-0.18, 0.04)}M${P(-0.18, -0.2)}L${P(-0.42, 0.04)}M${P(0.18, -0.2)}L${P(0.42, 0.04)}M${P(0.42, -0.2)}L${P(0.18, 0.04)}M${P(-0.18, 0.3)}L${P(0.18, 0.3)}" ${line}/>`;
    }
    return s;
  }

  function howtoArt() {
    const NAVY = '#120b28';
    const f = (v) => +v.toFixed(1);
    const stone = stoneSvg;
    // A patch of board: cols x rows points, cell c, origin at the first point.
    const floor = (x, y, cols, rows, c) => {
      let s = `<rect x="${x - c * 0.6}" y="${y - c * 0.6}" width="${(cols - 1 + 1.2) * c}" height="${(rows - 1 + 1.2) * c}" rx="${c * 0.4}" fill="#e9e5f0"/>`;
      s += `<g stroke="#2a1f4d" stroke-opacity="0.38" stroke-width="1.2" stroke-linecap="round">`;
      for (let i = 0; i < rows; i++) s += `<line x1="${x}" y1="${y + i * c}" x2="${x + (cols - 1) * c}" y2="${y + i * c}"/>`;
      for (let i = 0; i < cols; i++) s += `<line x1="${x + i * c}" y1="${y}" x2="${x + i * c}" y2="${y + (rows - 1) * c}"/>`;
      return s + '</g>';
    };
    const eye = (x, y, w) => `<path d="M${x - w},${y}Q${x},${y - w * 1.25} ${x + w},${y}Q${x},${y + w * 1.25} ${x - w},${y}Z" fill="#fff" stroke="${NAVY}" stroke-width="1.6"/><circle cx="${x}" cy="${y}" r="${f(w * 0.5)}" fill="${NAVY}"/>`;
    const svg = (body) => `<svg class="howto-art" viewBox="0 0 72 54" aria-hidden="true">${body}</svg>`;
    const turns = svg(stone(20, 27, 12, 'me') + stone(52, 27, 12, 'cpu')
      + `<path d="M24,11Q36,2 48,11M48,43Q36,52 24,43" fill="none" stroke="#fff" stroke-width="2.4" stroke-linecap="round"/>`
      + `<path d="M44,6L48.5,11.5L42,13M28,48L23.5,42.5L30,41" fill="none" stroke="#fff" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"/>`);
    let blobs = '';
    for (const [x, y, r] of [[36, 27, 17], [22, 18, 8], [51, 36, 9], [24, 39, 7], [50, 15, 6], [14, 30, 4]]) blobs += `<circle cx="${x}" cy="${y}" r="${r}" style="fill:var(--me)" opacity="0.55"/>`;
    const ink = svg(floor(12, 9, 4, 3, 16) + blobs + stone(36, 27, 11, 'me'));
    const capture = svg(floor(18, 9, 3, 3, 18) + stone(36, 27, 8, 'grey', 'dead')
      + stone(36, 9, 8, 'me') + stone(18, 27, 8, 'me') + stone(54, 27, 8, 'me') + stone(36, 45, 8, 'me'));
    let koArt = floor(15, 9, 4, 3, 14);
    for (const [x, y] of [[1, 0], [0, 1], [2, 1], [1, 2]]) koArt += stone(15 + x * 14, 9 + y * 14, 6.2, 'me');
    for (const [x, y] of [[2, 0], [3, 1], [2, 2]]) koArt += stone(15 + x * 14, 9 + y * 14, 6.2, 'cpu');
    koArt += `<circle cx="29" cy="23" r="5.6" fill="none" stroke="#fff" stroke-width="1.6" stroke-dasharray="2.6 2"/><path d="M26,20L32,26M32,20L26,26" stroke="#ff3b5c" stroke-width="2" stroke-linecap="round"/>`;
    const ko = svg(koArt);
    let ring = floor(8, 9, 5, 3, 14);
    for (let i = 0; i < 5; i++) ring += stone(8 + i * 14, 9, 6.4, 'me', 'beam') + stone(8 + i * 14, 37, 6.4, 'me', 'beam');
    ring += stone(8, 23, 6.4, 'me', 'beam') + stone(36, 23, 6.4, 'me', 'beam') + stone(64, 23, 6.4, 'me', 'beam');
    ring += eye(22, 23, 5) + eye(50, 23, 5);
    const eyes = svg(ring);
    let end = floor(12, 9, 4, 3, 16);
    end += `<rect x="2" y="0" width="34" height="54" style="fill:var(--me)" opacity="0.5"/>`;
    end += stone(28, 27, 7.5, 'grey', 'dead');
    for (const [x, y] of [[12, 27], [28, 9], [28, 45], [44, 27]]) end += `<circle cx="${x}" cy="${y}" r="7" style="fill:var(--me-light)" fill-opacity="0.8" stroke="${NAVY}" stroke-width="1.4" stroke-dasharray="3 2.4"/>`;
    end += stone(60, 9, 7.5, 'cpu') + stone(60, 45, 7.5, 'cpu');
    const endArt = svg(`<clipPath id="howto-end"><rect x="2" y="0" width="70" height="54" rx="7"/></clipPath><g clip-path="url(#howto-end)">${end}</g>`);
    const bar = (x, w, cls) => `<rect x="${x}" y="21" width="${w}" height="12" class="${cls}"/>`;
    const score = svg(`<defs><pattern id="howto-dots" width="5" height="5" patternUnits="userSpaceOnUse"><rect width="5" height="5" style="fill:var(--me)"/><circle cx="2.5" cy="2.5" r="1.2" fill="#fff" opacity="0.65"/></pattern>`
      + `<pattern id="howto-stripes" width="5" height="5" patternUnits="userSpaceOnUse" patternTransform="rotate(45)"><rect width="5" height="5" style="fill:var(--cpu)"/><rect width="2" height="5" style="fill:var(--cpu-light)"/></pattern>`
      + `<clipPath id="howto-bar"><rect x="4" y="21" width="64" height="12" rx="6"/></clipPath></defs>`
      + `<rect x="2" y="19" width="68" height="16" rx="8" fill="${NAVY}"/><g clip-path="url(#howto-bar)">`
      + bar(4, 26, 'ha-me') + bar(30, 10, 'ha-dots') + bar(40, 8, 'ha-stripes') + bar(48, 20, 'ha-cpu') + '</g>'
      + `<rect x="34.5" y="16" width="3" height="22" fill="#fff" stroke="${NAVY}" stroke-width="1"/>`
      + stone(14, 8, 5.5, 'me') + stone(58, 8, 5.5, 'cpu'));
    return [turns, ink, capture, ko, eyes, endArt, score];
  }
  {
    const items = $('howto-list').children;
    howtoArt().forEach((art, i) => { if (items[i]) items[i].insertAdjacentHTML('afterbegin', art); });
  }

  // Until the first look at the rules (and the first game), the button wiggles a little.
  if (store.get('howtoSeen', '0') !== '1' && !Object.keys(loadRecord()).length) $('howto-open').classList.add('nudge');
  // When the list doesn't fit (small frames), its bottom fades out until it is scrolled down.
  const howtoList = $('howto-list');
  function howtoFade() {
    const more = howtoList.scrollHeight - howtoList.clientHeight - howtoList.scrollTop > 4;
    howtoList.classList.toggle('more', more);
  }
  howtoList.addEventListener('scroll', howtoFade, { passive: true });
  addEventListener('resize', () => { if (!$('howto').hidden) howtoFade(); });
  $('howto-open').addEventListener('click', () => {
    $('howto').hidden = false;
    howtoList.scrollTop = 0;
    howtoFade();
    $('howto-open').classList.remove('nudge');
    store.set('howtoSeen', '1');
  });
  $('howto-close').addEventListener('click', () => { $('howto').hidden = true; });
  $('howto').addEventListener('click', (e) => { if (e.target === e.currentTarget) e.currentTarget.hidden = true; });

  const muteBtn = $('mute');
  function syncMute() { muteBtn.setAttribute('aria-pressed', sound.muted ? 'true' : 'false'); }
  muteBtn.addEventListener('click', () => {
    sound.muted = !sound.muted;
    store.set('muted', sound.muted ? '1' : '0');
    syncMute();
    if (!sound.muted) { sound.ensure(); sound.splat(1, 0.6); }
  });
  syncMute();

  const levelBtns = document.querySelectorAll('.levels button');
  function syncLevel() {
    levelBtns.forEach((b) => b.setAttribute('aria-checked', b.dataset.level === level ? 'true' : 'false'));
    const n = LEVELS[level].size;
    const hc = LEVELS[level].handicapKomi;
    $('level-note').textContent = hc != null
      ? t('levelNoteHandicap', { n, komi: BOARDS[n].komi, hc })
      : t('levelNote', { n, komi: BOARDS[n].komi });
    const rec = loadRecord()[level];
    $('level-record').textContent = !rec ? '' : t('record', rec) + (rec.s >= 2 ? ' · ' + t('streakNow', { n: rec.s }) : '');
  }
  levelBtns.forEach((b) => b.addEventListener('click', () => {
    level = b.dataset.level;
    store.set('level', level);
    syncLevel();
    sound.ensure();
    sound.splat(1.2, 0.5);
  }));
  syncLevel();

  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') { $('howto').hidden = true; }
  });

  // ---------- title art ----------

  function drawTitle() {
    const sp = $('title-splats');
    sp.textContent = '';
    const seed = (Math.random() * 1e9) | 0;
    splatGroup(sp, 30, 60, 90, COLORS.cpu, seed + 1, 0.05);
    splatGroup(sp, 380, 30, 60, COLORS.me, seed + 2, 0.15);
    splatGroup(sp, 410, 660, 115, COLORS.me, seed + 3, 0.25);
    splatGroup(sp, 0, 560, 60, COLORS.cpu, seed + 4, 0.35);
    splatGroup(sp, 390, 330, 34, COLORS.cpu, seed + 5, 0.45);
    sp.querySelectorAll('.sp').forEach((g) => g.setAttribute('opacity', '0.9'));

    const ls = $('logo-splat');
    ls.textContent = '';
    const g1 = splatGroup(ls, 150, 110, 78, COLORS.me, seed + 6, 0);
    const g2 = splatGroup(ls, 262, 114, 68, COLORS.cpu, seed + 7, 0.08);
    g1.setAttribute('class', 'sp');
    g2.setAttribute('class', 'sp');
    // Drips under the splats.
    for (const [x, y, h, c] of [[122, 160, 30, COLORS.me], [178, 164, 18, COLORS.me], [286, 158, 24, COLORS.cpu]]) {
      el('path', { d: `M${x - 9},${y} L${x + 9},${y} L${x + 7},${y + h} A7,7 0 0 1 ${x - 7},${y + h} Z`, fill: c }, ls);
      el('circle', { cx: x, cy: y + h + 2, r: 8, fill: c }, ls);
    }
  }

  // Show the title once its fonts are in, or after a short wait on a slow connection.
  function revealTitle() {
    const root = document.documentElement;
    const sheets = [...document.querySelectorAll('link[rel="stylesheet"][href*="fonts.googleapis"]')]
      .map((l) => l.sheet || new Promise((r) => { l.addEventListener('load', r); l.addEventListener('error', r); }));
    const text = $('title').textContent;
    const fonts = Promise.all(sheets).then(() => document.fonts && document.fonts.load &&
      Promise.all(['--font-logo', '--font-head', '--font-body'].map((v) => document.fonts.load(`800 32px ${cssVar(v)}`, text).catch(() => null))));
    Promise.race([fonts, wait(1500)]).then(() => root.classList.remove('fonts-wait'));
  }

  useSize(LEVELS[level].size);
  drawTitle();
  revealTitle();
  // Start the workers while the title is up, so the first move doesn't wait for them.
  setTimeout(() => {
    while (workersOk && pool.length < POOL_SIZE) if (!spawn()) break;
  }, 1200);

  // Debug/inspection hook for automated checks.
  window.__stoon = {
    get state() { return state; },
    get board() { return board; },
    get endReason() { return endReason; },
    start: startGame,
    play: (x, y) => playerMove(idx(x, y)),
    // Where the point (x, y) is on the screen (for tests that tap it).
    spot: (x, y) => {
      const svg = $('board');
      const pt = svg.createSVGPoint();
      pt.x = MARGIN + x * CELL;
      pt.y = MARGIN + y * CELL;
      const q = pt.matrixTransform(svg.getScreenCTM());
      return { x: q.x, y: q.y };
    },
    pass: playerPass,
    finish: (reason) => finish(reason || 'settled'),
    sound,
    get shareImage() { return shareImage; },
    get lastResult() { return lastResult; },
  };
})();
