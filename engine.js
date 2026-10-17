// stoon engine: Go rules for small boards (5x5, 7x7), area scoring, MCTS (UCT + RAVE) with ownership estimates.
(function (root) {
  'use strict';

  // Everything that depends on the board size lives in one engine per size.
  function build(N) {
    const W = N + 2;
    const SIZE = W * W;
    const PASS = -1;
    const EMPTY = 0, BLACK = 1, WHITE = 2, EDGE = 3;
    const DIRS = [1, -1, W, -W];
    const DIAGS = [W + 1, W - 1, -W + 1, -W - 1];

    const POINTS = [];
    for (let y = 0; y < N; y++) for (let x = 0; x < N; x++) POINTS.push((y + 1) * W + (x + 1));

    const idx = (x, y) => (y + 1) * W + (x + 1);
    const xOf = (p) => (p % W) - 1;
    const yOf = (p) => ((p / W) | 0) - 1;

    // Shared scratch for flood fills (single-threaded). Each fill marks points with a new
    // stamp; before the counter outgrows the marks (a long session runs billions of
    // fills) the marks are cleared and it starts over, or a fill would never end.
    const mark = new Int32Array(SIZE);
    const stack = new Int32Array(SIZE);
    let stamp = 0;
    function nextStamp() {
      if (++stamp >= 0x7fffffff) { mark.fill(0); stamp = 1; }
      return stamp;
    }

    let seed = (Date.now() ^ 0x9e3779b9) >>> 0 || 1;
    function rand() {
      seed ^= seed << 13; seed >>>= 0;
      seed ^= seed >>> 17;
      seed ^= seed << 5; seed >>>= 0;
      return seed / 4294967296;
    }
    function setSeed(s) { seed = (s >>> 0) || 1; }

    class Board {
      constructor() {
        this.c = new Int8Array(SIZE).fill(EDGE);
        for (const p of POINTS) this.c[p] = EMPTY;
        this.turn = BLACK;
        this.ko = -1;
        this.passes = 0;
        this.moves = 0;
        this.last = PASS;
        this.prisoners = [0, 0, 0]; // stones captured by black [1] and by white [2]
      }

      clone() {
        const b = new Board();
        b.copyFrom(this);
        return b;
      }

      copyFrom(o) {
        this.c.set(o.c);
        this.turn = o.turn;
        this.ko = o.ko;
        this.passes = o.passes;
        this.moves = o.moves;
        this.last = o.last;
        this.prisoners[1] = o.prisoners[1];
        this.prisoners[2] = o.prisoners[2];
      }

      hasLib(p) {
        const c = this.c, color = c[p];
        // Most groups have a liberty right next to the stone asked about.
        if (c[p + 1] === EMPTY || c[p - 1] === EMPTY || c[p + W] === EMPTY || c[p - W] === EMPTY) return true;
        nextStamp();
        let sp = 0;
        stack[sp++] = p;
        mark[p] = stamp;
        while (sp) {
          const q = stack[--sp];
          for (let k = 0; k < 4; k++) {
            const r = q + DIRS[k];
            const v = c[r];
            if (v === EMPTY) return true;
            if (v === color && mark[r] !== stamp) { mark[r] = stamp; stack[sp++] = r; }
          }
        }
        return false;
      }

      // The only liberty of the group at p, or -1 when it has two or more.
      soleLib(p) {
        const c = this.c, color = c[p];
        let open = 0;
        for (let k = 0; k < 4; k++) if (c[p + DIRS[k]] === EMPTY) open++;
        if (open >= 2) return -1;
        nextStamp();
        let sp = 0, lib = -1;
        stack[sp++] = p;
        mark[p] = stamp;
        while (sp) {
          const q = stack[--sp];
          for (let k = 0; k < 4; k++) {
            const r = q + DIRS[k];
            const v = c[r];
            if (v === EMPTY) {
              if (lib === -1) lib = r;
              else if (lib !== r) return -1;
            } else if (v === color && mark[r] !== stamp) { mark[r] = stamp; stack[sp++] = r; }
          }
        }
        return lib;
      }

      // Stones and liberty count of the group at p.
      group(p) {
        const c = this.c, color = c[p];
        const stones = [];
        const libs = new Set();
        nextStamp();
        let sp = 0;
        stack[sp++] = p;
        mark[p] = stamp;
        while (sp) {
          const q = stack[--sp];
          stones.push(q);
          for (let k = 0; k < 4; k++) {
            const r = q + DIRS[k];
            const v = c[r];
            if (v === EMPTY) libs.add(r);
            else if (v === color && mark[r] !== stamp) { mark[r] = stamp; stack[sp++] = r; }
          }
        }
        return { stones, libs: libs.size };
      }

      remove(p, out) {
        const c = this.c, color = c[p];
        let sp = 0, n = 0;
        stack[sp++] = p;
        c[p] = EMPTY;
        while (sp) {
          const q = stack[--sp];
          n++;
          if (out) out.push(q);
          for (let k = 0; k < 4; k++) {
            const r = q + DIRS[k];
            if (c[r] === color) { c[r] = EMPTY; stack[sp++] = r; }
          }
        }
        return n;
      }

      // Plays the move for this.turn. Returns false (board unchanged) if illegal.
      play(p, captured) {
        if (p === PASS) {
          this.ko = -1;
          this.last = PASS;
          this.passes++;
          this.turn = 3 - this.turn;
          this.moves++;
          return true;
        }
        const c = this.c;
        if (c[p] !== EMPTY || p === this.ko) return false;
        const me = this.turn, op = 3 - me;
        c[p] = me;
        let cap = 0, capPt = -1;
        for (let k = 0; k < 4; k++) {
          const q = p + DIRS[k];
          if (c[q] === op && !this.hasLib(q)) { cap += this.remove(q, captured); capPt = q; }
        }
        if (cap === 0 && !this.hasLib(p)) { c[p] = EMPTY; return false; }
        this.prisoners[me] += cap;
        this.ko = -1;
        if (cap === 1) {
          let alone = true, libs = 0;
          for (let k = 0; k < 4; k++) {
            const v = c[p + DIRS[k]];
            if (v === me) alone = false;
            else if (v === EMPTY) libs++;
          }
          if (alone && libs === 1) this.ko = capPt;
        }
        this.passes = 0;
        this.last = p;
        this.turn = op;
        this.moves++;
        return true;
      }

      isLegal(p) {
        if (p === PASS) return true;
        const c = this.c;
        if (c[p] !== EMPTY || p === this.ko) return false;
        if (c[p + 1] === EMPTY || c[p - 1] === EMPTY || c[p + W] === EMPTY || c[p - W] === EMPTY) return true;
        // Try the stone in place (taken back after): legal if it captures or keeps a liberty.
        const op = 3 - this.turn;
        c[p] = this.turn;
        let ok = false;
        for (let k = 0; k < 4 && !ok; k++) {
          const q = p + DIRS[k];
          if (c[q] === op && !this.hasLib(q)) ok = true;
        }
        if (!ok) ok = this.hasLib(p);
        c[p] = EMPTY;
        return ok;
      }

      // True single-point eye shape for color (filling it is never useful in playouts).
      isEye(p, color) {
        const c = this.c;
        for (let k = 0; k < 4; k++) {
          const v = c[p + DIRS[k]];
          if (v !== color && v !== EDGE) return false;
        }
        let bad = 0, edge = 0;
        for (let k = 0; k < 4; k++) {
          const v = c[p + DIAGS[k]];
          if (v === EDGE) edge = 1;
          else if (v === 3 - color) bad++;
        }
        return edge ? bad === 0 : bad < 2;
      }

      // Area score black - white (no komi) with every empty region credited to its sole
      // bordering color. Writes +1/-1/0 per point into own if given.
      areaScore(own) {
        const c = this.c;
        let score = 0;
        nextStamp();
        const regionStamp = stamp;
        for (let i = 0; i < POINTS.length; i++) {
          const p = POINTS[i];
          const v = c[p];
          if (v === BLACK) { score++; if (own) own[p] = 1; continue; }
          if (v === WHITE) { score--; if (own) own[p] = -1; continue; }
          if (mark[p] === regionStamp) continue;
          // Flood the empty region.
          const region = [];
          let sp = 0, borders = 0;
          stack[sp++] = p;
          mark[p] = regionStamp;
          while (sp) {
            const q = stack[--sp];
            region.push(q);
            for (let k = 0; k < 4; k++) {
              const r = q + DIRS[k];
              const w = c[r];
              if (w === EMPTY) { if (mark[r] !== regionStamp) { mark[r] = regionStamp; stack[sp++] = r; } }
              else if (w === BLACK) borders |= 1;
              else if (w === WHITE) borders |= 2;
            }
          }
          const owner = borders === 1 ? 1 : borders === 2 ? -1 : 0;
          score += owner * region.length;
          if (own) for (const q of region) own[q] = owner;
        }
        return score;
      }
    }

    const scratch2 = new Board();
    const empties = new Int32Array(POINTS.length);
    const PTS = Int32Array.from(POINTS); // the same points, for the play-out's hot loop

    // Playing p would leave a group of 2+ stones with a single liberty and capture nothing.
    function badSelfAtari(b, p) {
      const c = b.c;
      let open = 0;
      for (let k = 0; k < 4; k++) if (c[p + DIRS[k]] === EMPTY) open++;
      if (open >= 2) return false;
      if (c[p] !== EMPTY || p === b.ko) return true; // not playable at all
      // Try the stone in place (taken back after).
      const me = b.turn, op = 3 - me;
      c[p] = me;
      let bad = false, captures = false;
      for (let k = 0; k < 4 && !captures; k++) {
        const q = p + DIRS[k];
        if (c[q] === op && !b.hasLib(q)) captures = true;
      }
      if (!captures) {
        if (!b.hasLib(p)) bad = true; // suicide
        else if (b.soleLib(p) !== -1) {
          // In atari: bad when it joined stones of ours (a lone stone may be a throw-in).
          for (let k = 0; k < 4; k++) if (c[p + DIRS[k]] === me) bad = true;
        }
      }
      c[p] = EMPTY;
      return bad;
    }

    // Answer the last move: capture a group it left in atari, or save one of ours it put in atari.
    function tactical(b) {
      const last = b.last;
      if (last === PASS) return PASS;
      const c = b.c, me = b.turn, op = 3 - me;
      if (c[last] === op) {
        const lib = b.soleLib(last);
        if (lib >= 0 && b.play(lib)) return lib;
      }
      for (let k = 0; k < 4; k++) {
        const q = last + DIRS[k];
        if (c[q] !== me) continue;
        const lib = b.soleLib(q);
        if (lib >= 0 && !b.isEye(lib, me) && !badSelfAtari(b, lib) && b.play(lib)) return lib;
      }
      return PASS;
    }

    // Playout move for b.turn: tactics first, then random among moves that don't fill its
    // own eye or self-atari a group. Plays it and returns it.
    function playRandom(b) {
      if (rand() < 0.9) {
        const t = tactical(b);
        if (t !== PASS) return t;
      }
      const c = b.c, me = b.turn;
      let n = 0;
      for (let i = 0; i < PTS.length; i++) {
        const q = PTS[i];
        if (c[q] === EMPTY) empties[n++] = q;
      }
      while (n) {
        const j = (rand() * n) | 0;
        const p = empties[j];
        empties[j] = empties[--n];
        if (b.isEye(p, me) || p === b.ko) continue;
        if (badSelfAtari(b, p)) continue;
        if (b.play(p)) return p;
      }
      b.play(PASS);
      return PASS;
    }

    // Longest simulation (tree moves + play-out) from the searched position.
    const MAX_SIM = 160;

    class Node {
      constructor(move, color, parent) {
        this.move = move;
        this.color = color; // color that played move
        this.parent = parent;
        this.children = null;
        this.n = 0; this.w = 0;
        this.an = 0; this.aw = 0;
      }
    }

    class Search {
      constructor(board, komi) {
        this.board = board.clone();
        this.limit = board.moves + MAX_SIM;
        this.komi = komi;
        this.root = new Node(PASS, 3 - board.turn, null);
        this.ownSum = new Float64Array(SIZE);
        this.count = 0;
        this.work = new Board();
        this.own = new Int8Array(SIZE);
        this.amaf = new Int8Array(SIZE);
        this.path = [];
      }

      expand(node, b) {
        const kids = [];
        const me = b.turn;
        for (const p of POINTS) {
          if (b.c[p] !== EMPTY || b.isEye(p, me)) continue;
          if (b.isLegal(p)) kids.push(new Node(p, me, node));
        }
        kids.push(new Node(PASS, me, node));
        node.children = kids;
      }

      select(node) {
        let best = null, bestV = -1;
        const logN = Math.log(node.n + 1);
        const kids = node.children;
        for (let i = 0; i < kids.length; i++) {
          const ch = kids[i];
          let v;
          if (ch.n === 0 && ch.an === 0) {
            v = ch.move === PASS ? 0.5 : 1.0 + rand() * 0.01;
          } else {
            const q = ch.n ? ch.w / ch.n : 0.5;
            let mix = q;
            if (ch.an) {
              const beta = ch.an / (ch.n + ch.an + ch.n * ch.an * 0.001 + 1e-9);
              mix = (1 - beta) * q + beta * (ch.aw / ch.an);
            }
            v = mix + 0.2 * Math.sqrt(logN / (ch.n + 1));
          }
          if (v > bestV) { bestV = v; best = ch; }
        }
        return best;
      }

      iterate() {
        const b = this.work;
        b.copyFrom(this.board);
        const path = this.path;
        path.length = 0;
        const amaf = this.amaf;
        amaf.fill(0);
        let node = this.root;
        path.push(node);
        while (node.children && b.passes < 2) {
          node = this.select(node);
          const color = b.turn;
          b.play(node.move);
          if (node.move !== PASS && !amaf[node.move]) amaf[node.move] = color;
          path.push(node);
        }
        if (!node.children && b.passes < 2 && b.moves < this.limit && (node.n >= 1 || node === this.root)) {
          this.expand(node, b);
          node = this.select(node);
          const color = b.turn;
          b.play(node.move);
          if (node.move !== PASS && !amaf[node.move]) amaf[node.move] = color;
          path.push(node);
        }
        // Two passes don't end the simulation: the board as it stands may still hold dead
        // stones and open borders, so the play-out settles them before the count.
        if (b.passes >= 2) b.passes = 0;
        while (b.passes < 2 && b.moves < this.limit) {
          const color = b.turn;
          const p = playRandom(b);
          if (p !== PASS && !amaf[p]) amaf[p] = color;
        }
        const own = this.own, ownSum = this.ownSum;
        const rb = b.areaScore(own) - this.komi > 0 ? 1 : 0; // reward for black
        const rw = 1 - rb;
        for (let i = 0; i < POINTS.length; i++) ownSum[POINTS[i]] += own[POINTS[i]];
        this.count++;
        for (let i = 0; i < path.length; i++) {
          const nd = path[i];
          nd.n++;
          nd.w += nd.color === BLACK ? rb : rw;
          const kids = nd.children;
          if (!kids) continue;
          for (let j = 0; j < kids.length; j++) {
            const ch = kids[j];
            if (ch.move !== PASS && amaf[ch.move] === ch.color) {
              ch.an++;
              ch.aw += ch.color === BLACK ? rb : rw;
            }
          }
        }
      }

      run(iterations) {
        for (let i = 0; i < iterations; i++) this.iterate();
      }

      // Ownership per point, +1 = black, -1 = white.
      ownership() {
        const out = new Float32Array(SIZE);
        if (!this.count) return out;
        for (const p of POINTS) out[p] = this.ownSum[p] / this.count;
        return out;
      }

      // Children sorted by visits: [{move, n, winrate}] from the mover's point of view.
      ranked() {
        if (!this.root.children) return [];
        return this.root.children
          .filter((c) => c.n > 0)
          .map((c) => ({ move: c.move, n: c.n, winrate: c.w / c.n }))
          .sort((a, b) => b.n - a.n);
      }

      // Win probability for the side to move at the root.
      winrate() {
        const r = this.root;
        return r.n ? 1 - r.w / r.n : 0.5;
      }
    }

    // Light playouts underrate big living groups, so a stone counts as dead as soon as the
    // estimate leans clearly to the other side; near-zero stones (seki, fights) stay alive.
    const DEAD_LEAN = 0.15;

    // Mean ownership of each group, seen from the group's own color (+1 = surely alive).
    function groupLean(board, own) {
      const lean = new Float32Array(SIZE);
      const seen = new Uint8Array(SIZE);
      for (const p of POINTS) {
        const v = board.c[p];
        if (v === EMPTY || seen[p]) continue;
        const { stones } = board.group(p);
        let sum = 0;
        for (const q of stones) { seen[q] = 1; sum += own[q]; }
        const m = (v === BLACK ? sum : -sum) / stones.length;
        for (const q of stones) lean[q] = m;
      }
      return lean;
    }

    // Area score with dead stones taken from the ownership estimate (what the CPU expects
    // the count to be). Returns {black, white, owner: Int8Array(+1/-1/0 per point), dead}.
    function judge(board, own) {
      const b = board.clone();
      const dead = deadStones(board, own);
      for (const p of dead) b.c[p] = EMPTY;
      const owner = new Int8Array(SIZE);
      b.areaScore(owner);
      // Regions bordered by both colors: fall back to the estimate point by point.
      for (const p of POINTS) {
        if (b.c[p] === EMPTY && owner[p] === 0) owner[p] = own[p] > 0.3 ? 1 : own[p] < -0.3 ? -1 : 0;
      }
      let black = 0, white = 0;
      for (const p of POINTS) {
        if (owner[p] > 0) black++;
        else if (owner[p] < 0) white++;
      }
      return { black, white, owner, dead };
    }

    // Empty regions of a board array: [{points, borders (1 black, 2 white, 3 both), touching
    // (stones next to the region)}]. Plain arrays, so the flood-fill scratch is free after.
    function regionsOf(c) {
      const out = [];
      const st = nextStamp();
      for (const p of POINTS) {
        if (c[p] !== EMPTY || mark[p] === st) continue;
        const points = [], touching = [];
        let sp = 0, borders = 0;
        stack[sp++] = p;
        mark[p] = st;
        while (sp) {
          const q = stack[--sp];
          points.push(q);
          for (let k = 0; k < 4; k++) {
            const r = q + DIRS[k];
            const w = c[r];
            if (w === EMPTY) { if (mark[r] !== st) { mark[r] = st; stack[sp++] = r; } }
            else if (w === BLACK || w === WHITE) { borders |= w; touching.push(r); }
          }
        }
        out.push({ points, borders, touching });
      }
      return out;
    }

    // Whether color could fill the empty point p in play: legal, not its own eye, and not
    // putting its own group in atari (the shared liberties of a seki, its own last space)
    // unless one move of its own first makes that safe.
    function canFill(board, p, color) {
      const turn = board.turn, ko = board.ko;
      board.turn = color;
      if (color !== turn) board.ko = -1;
      const ok = !board.isEye(p, color) && board.isLegal(p) && (!badSelfAtari(board, p) || fillsAfterJoining(board, p, color));
      board.turn = turn;
      board.ko = ko;
      return ok;
    }

    // Filling p would leave color's group in atari, but color can first play that group's
    // last other liberty without putting anything in atari (say, joining a cut-off stone
    // to its wall through its own ground) and then fill p safely. Looking one move ahead
    // only, such a point looks like a seki and the group behind it like it lives.
    function fillsAfterJoining(board, p, color) {
      const b = scratch2;
      b.copyFrom(board);
      b.turn = color;
      b.ko = -1;
      if (!b.play(p)) return false;
      const lib = b.soleLib(p);
      if (lib < 0) return false;
      b.copyFrom(board);
      b.turn = color;
      b.ko = -1;
      if (!b.play(lib) || b.group(lib).libs < 2) return false;
      b.turn = color;
      b.ko = -1;
      return b.play(p) && b.group(p).libs >= 2;
    }

    // Groups that look like seki: they touch a point between the colors that neither side
    // can fill without putting its own group in atari. sekiStatus reads them out.
    function sekiCandidates(board) {
      const seki = new Set();
      for (const r of regionsOf(board.c)) {
        if (r.borders !== 3) continue;
        for (const q of r.points) {
          if (canFill(board, q, BLACK) || canFill(board, q, WHITE)) continue;
          for (let k = 0; k < 4; k++) {
            const s = q + DIRS[k];
            if ((board.c[s] === BLACK || board.c[s] === WHITE) && !seki.has(s)) {
              for (const t of board.group(s).stones) seki.add(t);
            }
          }
        }
      }
      return seki;
    }

    // How far and how long a seki is read out (plies, positions), and the most empty points
    // the fight may use (a wider one is a game still going on, not a seki to confirm).
    const READ_DEPTH = 24, READ_NODES = 10000, READ_ROOM = 10;
    let readLeft = 0; // positions left for all the groups of one board

    // The points a local fight around a group can use: the empty regions next to it (up to
    // 8 points), then the small ones (1-2 points) next to the stones those touch, two steps
    // out (a side may first join cut-off stones to its wall), the stones themselves (their
    // points are freed when they are taken), enemy stones short of liberties next to them
    // (taking those gains liberties), and every liberty of the short-of-liberty groups
    // among them (a ring of groups in seki defends by threatening to take the next).
    function readingArea(board, stones) {
      const regions = regionsOf(board.c);
      const regionOf = new Int32Array(SIZE).fill(-1);
      regions.forEach((r, i) => { for (const q of r.points) regionOf[q] = i; });
      const inArea = new Uint8Array(SIZE), used = new Uint8Array(regions.length);
      for (const t of stones) inArea[t] = 1;
      let frontier = stones;
      for (let step = 0; step < 3 && frontier.length; step++) {
        const next = [];
        for (const t of frontier) {
          for (let k = 0; k < 4; k++) {
            const i = regionOf[t + DIRS[k]];
            if (i < 0 || used[i] || regions[i].points.length > (step ? 2 : 8)) continue;
            used[i] = 1;
            for (const q of regions[i].points) inArea[q] = 1;
            for (const u of regions[i].touching) {
              if (inArea[u]) continue;
              for (const v of board.group(u).stones) { inArea[v] = 1; next.push(v); }
            }
          }
        }
        frontier = next;
      }
      // Enemy stones short of liberties right next to the area can be taken for liberties.
      for (const q of POINTS.filter((t) => inArea[t] && board.c[t] !== EMPTY)) {
        for (let k = 0; k < 4; k++) {
          const r = q + DIRS[k];
          if (inArea[r] || board.c[r] !== 3 - board.c[q]) continue;
          const g = board.group(r);
          if (g.libs <= 2) for (const t of g.stones) inArea[t] = 1;
        }
      }
      const seen = new Uint8Array(SIZE);
      for (const q of POINTS) {
        if (!inArea[q] || board.c[q] === EMPTY || seen[q]) continue;
        const g = board.group(q);
        for (const t of g.stones) seen[t] = 1;
        if (g.libs > 3) continue;
        for (const t of g.stones) for (let k = 0; k < 4; k++) if (board.c[t + DIRS[k]] === EMPTY) inArea[t + DIRS[k]] = 1;
      }
      return POINTS.filter((q) => inArea[q]);
    }

    // Whether the group at p can be taken by force: its opponent moves first (or its owner,
    // with ownerFirst), the other answers, both only inside area (or pass). true or false,
    // null if the reading ran out.
    function capturable(board, p, area, ownerFirst) {
      const color = board.c[p];
      const plies = [];
      for (let i = 0; i <= READ_DEPTH; i++) plies.push(new Board());
      const root = plies[READ_DEPTH];
      root.copyFrom(board);
      root.turn = ownerFirst ? color : 3 - color;
      root.ko = -1;
      root.passes = 0;
      const memo = new Map();
      let nodes = 0, out = false;
      const wins = (b, depth) => {
        if (b.c[p] !== color) return true;
        if (depth === 0 || b.passes >= 2) return false;
        // Each attacker stone takes one liberty at most: too many left for the plies left.
        const attacking = b.turn !== color;
        if (b.group(p).libs > (attacking ? depth + 1 : depth) >> 1) return false;
        if (++nodes > READ_NODES || --readLeft < 0) { out = true; return false; }
        let key = '';
        for (let i = 0; i < area.length; i++) key += b.c[area[i]];
        key += b.turn + ',' + b.ko + ',' + b.passes + ',' + depth;
        const hit = memo.get(key);
        if (hit !== undefined) return hit;
        const next = plies[depth - 1];
        let result = !attacking;
        for (let i = 0; i <= area.length; i++) {
          // The owner tries passing first (in a seki any move hurts), the attacker last.
          const m = attacking ? (i < area.length ? area[i] : PASS) : (i ? area[i - 1] : PASS);
          if (m !== PASS && (b.c[m] !== EMPTY || b.isEye(m, b.turn))) continue;
          next.copyFrom(b);
          if (!next.play(m)) continue;
          const w = wins(next, depth - 1);
          if (out) return false;
          if (w === attacking) { result = w; break; }
        }
        memo.set(key, result);
        return result;
      };
      const r = wins(root, READ_DEPTH);
      return out ? null : r;
    }

    // Seki, read out. A candidate group that its opponent can take by force, even when its
    // owner moves first, is dead, not in seki: say the attacker throws stones in, and the
    // space left once they are taken back holds only one eye; or it joins up a cut-off
    // stone before filling. One that can be taken only if the opponent moves first is
    // still being fought over (unsettled): not in seki, and the estimate decides. Returns
    // {seki, dead, unsettled}: Sets of stones. The last boards asked about are remembered
    // (the same board is asked about often).
    const sekiMemo = new Map();
    function sekiStatus(board) {
      const key = board.c.join('') + board.turn + ',' + board.ko;
      const hit = sekiMemo.get(key);
      if (hit) return hit;
      const cand = sekiCandidates(board);
      const seki = new Set(), dead = new Set(), unsettled = new Set();
      readLeft = 2 * READ_NODES;
      if (cand.size) {
        const groups = [];
        const seen = new Set();
        for (const s of cand) {
          if (seen.has(s)) continue;
          const g = board.group(s).stones;
          for (const t of g) seen.add(t);
          const area = readingArea(board, g);
          const room = area.filter((q) => board.c[q] === EMPTY).length;
          const taken = room > READ_ROOM ? null : capturable(board, s, area, false);
          const sure = taken === true && capturable(board, s, area, true) === true;
          groups.push({ stones: g, taken, sure });
        }
        for (const g of groups) {
          const into = g.taken !== true ? seki : g.sure ? dead : unsettled;
          for (const t of g.stones) into.add(t);
        }
        // Without the groups that can be taken, what is left may no longer be a seki.
        if (dead.size || unsettled.size) {
          const b = board.clone();
          for (const g of groups) if (g.taken === true) for (const t of g.stones) b.c[t] = EMPTY;
          const still = sekiCandidates(b);
          for (const t of [...seki]) if (!still.has(t)) seki.delete(t);
        }
      }
      const status = { seki, dead, unsettled };
      sekiMemo.set(key, status);
      if (sekiMemo.size > 32) sekiMemo.delete(sekiMemo.keys().next().value);
      return status;
    }

    // Stones of groups in seki.
    function sekiStones(board) {
      return sekiStatus(board).seki;
    }

    // The game is decided on the board: every stone's fate is clear and every empty
    // region belongs to a single living color (no dame left to fill). Groups in seki
    // live, and their shared liberties may stay empty.
    function isSettled(board, own) {
      const c = board.c;
      const lean = groupLean(board, own);
      const { seki, dead, unsettled } = sekiStatus(board);
      if (unsettled.size) return false;
      const alive = (p) => !dead.has(p) && (seki.has(p) || lean[p] >= -DEAD_LEAN);
      // Every group is clearly alive or clearly dead.
      for (const p of POINTS) {
        if (c[p] === EMPTY || seki.has(p) || dead.has(p)) continue;
        if (lean[p] <= 0.3 && lean[p] > -0.8) return false;
      }
      for (const r of regionsOf(c)) {
        let borders = 0, onlySeki = true;
        for (const s of r.touching) {
          borders |= alive(s) ? c[s] : 3 - c[s];
          if (!seki.has(s)) onlySeki = false;
        }
        if (borders === 0) return false;
        if (borders === 3) {
          if (r.points.some((q) => canFill(board, q, BLACK) || canFill(board, q, WHITE))) return false;
          continue;
        }
        if (onlySeki) continue; // an eye of a group in seki: nobody's territory
        // The estimate must agree that the region is that color's territory.
        let sum = 0, weakest = 1;
        for (const q of r.points) { sum += own[q]; weakest = Math.min(weakest, Math.abs(own[q])); }
        const m = (borders === 1 ? sum : -sum) / r.points.length;
        if (m < 0.45 || weakest < 0.3) return false;
      }
      // Any group in atari still has something to fight over.
      for (const p of POINTS) {
        if (c[p] !== EMPTY && alive(p) && board.group(p).libs === 1) return false;
      }
      return true;
    }

    // Some empty region still touches both colors with a point either side could fill
    // (dame, an open border, stones to take), or the board has no stones yet. The shared
    // liberties of a seki don't count. dead: stones to treat as already taken off.
    function hasOpenArea(board, dead) {
      let c = board.c;
      if (dead && dead.length) {
        c = c.slice();
        for (const p of dead) c[p] = EMPTY;
      }
      for (const r of regionsOf(c)) {
        if (r.borders === 0) return true;
        if (r.borders !== 3) continue;
        for (const q of r.points) {
          if (board.c[q] === EMPTY && (canFill(board, q, BLACK) || canFill(board, q, WHITE))) return true;
        }
      }
      return false;
    }

    // Every group with its eyes: [{color, stones, eyes: [[points] per eye]}]. An eye is an
    // empty region that only the group's color surrounds and that touches the group: two
    // points or more, or a single point that is a true eye (not a false eye).
    function groupsOf(board) {
      const c = board.c;
      const regions = regionsOf(c);
      const out = [];
      const seen = new Uint8Array(SIZE);
      for (const p of POINTS) {
        const v = c[p];
        if (v === EMPTY || seen[p]) continue;
        const { stones } = board.group(p);
        for (const q of stones) seen[q] = 1;
        const eyes = [];
        for (const r of regions) {
          if (r.borders !== v || !r.touching.some((s) => stones.includes(s))) continue;
          if (r.points.length >= 2 || board.isEye(r.points[0], v)) eyes.push(r.points);
        }
        out.push({ color: v, stones, eyes });
      }
      return out;
    }

    // Stones counted dead at the end: groups the ownership estimate gives to the other
    // side, except groups in seki and groups with two eyes, and groups that reading shows
    // the other side can take by force (see sekiStatus). Sorted.
    function deadStones(board, own) {
      const { seki, dead: taken } = sekiStatus(board);
      const lean = groupLean(board, own);
      const dead = [];
      for (const g of groupsOf(board)) {
        const p = g.stones[0];
        if (!taken.has(p) && (lean[p] >= -DEAD_LEAN || seki.has(p) || g.eyes.length >= 2)) continue;
        dead.push(...g.stones);
      }
      return dead.sort((a, b) => a - b);
    }

    // The game can end on its own: settled with either side to move (ownA, ownB are the
    // estimates with each side to move), and both agree on which stones are dead.
    function settledBoth(board, ownA, ownB) {
      if (!isSettled(board, ownA) || !isSettled(board, ownB)) return false;
      const a = deadStones(board, ownA), b = deadStones(board, ownB);
      return a.length === b.length && a.every((p, i) => p === b[i]);
    }

    // Final count. own: ownership estimate, best averaged over both sides to move. Dead
    // stones come from deadStones; territory is read off the board itself with them taken
    // off: an empty region that only one color surrounds is theirs; regions touching both
    // (dame, open borders, seki liberties) and the eyes of groups in seki are nobody's.
    // Returns {black, white, owner (+1/-1/0 per point, living stones included),
    // dead: [points], seki: [stone points]}.
    function judgeEnd(board, own) {
      const dead = deadStones(board, own);
      const b = board.clone();
      for (const p of dead) b.c[p] = EMPTY;
      const seki = sekiStones(b);
      const owner = new Int8Array(SIZE);
      for (const r of regionsOf(b.c)) {
        if (r.borders !== 1 && r.borders !== 2) continue;
        if (r.touching.every((s) => seki.has(s))) continue;
        for (const q of r.points) owner[q] = r.borders === 1 ? 1 : -1;
      }
      let black = 0, white = 0;
      for (const p of POINTS) {
        if (b.c[p] === BLACK) owner[p] = 1;
        else if (b.c[p] === WHITE) owner[p] = -1;
        if (owner[p] > 0) black++;
        else if (owner[p] < 0) white++;
      }
      return { black, white, owner, dead, seki: [...seki] };
    }

    // Japanese count of an ended game from judgeEnd's result: territory (the empty points
    // and dead stones' points a color surrounds) and prisoners (stones taken during the
    // game plus the dead stones), per color. Komi is left to the caller.
    // Returns {terr: [, black, white], age: [, black, white], black, white}.
    function countJapanese(board, j) {
      const dead = new Uint8Array(SIZE);
      for (const p of j.dead) dead[p] = 1;
      const terr = [0, 0, 0], age = [0, board.prisoners[BLACK], board.prisoners[WHITE]];
      for (const p of POINTS) {
        const v = board.c[p];
        if (v === EMPTY || dead[p]) {
          if (j.owner[p] > 0) terr[BLACK]++;
          else if (j.owner[p] < 0) terr[WHITE]++;
        }
        if (dead[p]) age[3 - v]++;
      }
      return { terr, age, black: terr[BLACK] + age[BLACK], white: terr[WHITE] + age[WHITE] };
    }

    // Point by point mean of two ownership estimates (one with each side to move).
    function average(a, b) {
      const out = new Float32Array(SIZE);
      for (const p of POINTS) out[p] = (a[p] + b[p]) / 2;
      return out;
    }

    // Weight for a timid player that fences in a little ground of its own: moves into the
    // other side's area, moves that touch the other side's stones (unless they capture or
    // save a group in atari) and moves away from its own stones are much less likely.
    function shyWeight(board, own, move) {
      const me = board.turn, c = board.c;
      let w = 1;
      const mine = me === BLACK ? own[move] : -own[move];
      if (mine < -0.4) w *= 0.1;
      let contact = false, urgent = false;
      for (let k = 0; k < 4; k++) {
        const q = move + DIRS[k];
        if (c[q] !== BLACK && c[q] !== WHITE) continue;
        if (board.group(q).libs === 1) urgent = true;
        if (c[q] !== me) contact = true;
      }
      if (contact && !urgent) w *= 0.15;
      let near = false, any = false;
      for (const p of POINTS) {
        if (c[p] !== me) continue;
        any = true;
        if (Math.abs(xOf(p) - xOf(move)) + Math.abs(yOf(p) - yOf(move)) <= 2) near = true;
      }
      if (any && !near) w *= 0.2;
      return w;
    }

    // What the side to move should do after a search.
    // opts.other: the estimate with the other side to move (the game makes one after the
    // opponent passes). Dead stones and open ground are then judged on the mean of the
    // two, as the final count does, and the game is decided only if both agree.
    // Returns {type: 'end'} when the game is decided on the board, otherwise
    // {type: 'move', move} (PASS included) or {type: 'resign'}.
    function decide(search, board, opts = {}) {
      const own = search.ownership();
      if (opts.other ? settledBoth(board, own, opts.other) : isSettled(board, own)) return { type: 'end' };
      const ranked = search.ranked();
      if (!ranked.length) return { type: 'move', move: PASS };
      const me = board.turn;
      const best = ranked[0];
      const both = opts.other ? average(own, opts.other) : own;
      // Dame or open borders left (the stones the estimate calls dead set aside).
      const open = hasOpenArea(board, deadStones(board, both));
      if (!open && board.passes > 0) {
        // The opponent passed and nothing is left to fill. With both sides' estimates,
        // pass back and let the count settle the stones, rather than throw stones into
        // ground the other side holds (they live when the opponent keeps passing).
        // With one estimate only, pass back when the count is already ours.
        if (opts.other) return { type: 'move', move: PASS };
        const n = countJapanese(board, judgeEnd(board, own));
        const margin = n.black - n.white - search.komi;
        if (best.winrate > 0.8 && (me === BLACK ? margin : -margin) > 0) return { type: 'move', move: PASS };
      }
      if (opts.resign && best.winrate < 0.03 && board.moves > 14 && search.count >= 2000) return { type: 'resign' };
      if (!open && board.moves >= POINTS.length / 2) {
        // Nothing left to fill (early on every empty area touches one color only, which
        // is why half a board of moves must come first). The search counts area, where a
        // stone in your own ground costs nothing; in the Japanese count it costs a point.
        // So pass, unless some move really does better than passing (saving or taking a
        // group).
        const pass = ranked.find((r) => r.move === PASS);
        if (pass && pass.n >= 30 && pass.winrate >= best.winrate - 0.04) return { type: 'move', move: PASS, winrate: best.winrate };
      }
      let pick = best;
      if (best.move === PASS && open) {
        // Don't hand the game over while there is shared ground left.
        const play = ranked.find((r) => r.move !== PASS);
        if (play) pick = play;
      }
      if (opts.temperature) {
        // Weaker play: sample among non-pass moves by visits.
        // Only moves the search found nearly as good (floor: share of the best one's visits).
        const floor = best.n * (opts.floor != null ? opts.floor : opts.shy ? 0.2 : 0);
        const pool = ranked.filter((r) => r.move !== PASS && r.n >= floor);
        if (pool.length && pick.move !== PASS) {
          const w = pool.map((r) => Math.pow(r.n, 1 / opts.temperature) * (opts.shy ? shyWeight(board, own, r.move) : 1));
          let t = rand() * w.reduce((a, b) => a + b, 0);
          for (let i = 0; i < pool.length; i++) { t -= w[i]; if (t <= 0) { pick = pool[i]; break; } }
        }
      }
      return { type: 'move', move: pick.move, winrate: best.winrate };
    }

    const api = { N, W, SIZE, PASS, EMPTY, BLACK, WHITE, EDGE, POINTS, idx, xOf, yOf, Board, Search, judge, judgeEnd, countJapanese, average, deadStones, sekiStones, groupsOf, isSettled, settledBoth, hasOpenArea, decide, setSeed, playRandom };
    return api;
  }

  const builds = {};
  const size = (n) => builds[n] || (builds[n] = build(n));
  // The default export is the 7x7 engine; size(n) gives the engine for an n x n board.
  const api = Object.assign({ size }, size(7));
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.Stoon = api;
})(this);
