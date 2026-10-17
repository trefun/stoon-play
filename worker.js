// stoon: runs searches off the main thread so the board keeps animating while the CPU
// thinks. One job at a time; a new job (or 'stop') abandons the current one.
importScripts('engine.js');

let current = 0;
// Yield between slices through a message channel: setTimeout(0) is clamped to 4 ms.
const tick = new MessageChannel();
let next = null;
tick.port1.onmessage = () => { const f = next; next = null; if (f) f(); };
const later = (f) => { next = f; tick.port2.postMessage(0); };

function boardOf(S, b) {
  const board = new S.Board();
  board.c.set(b.c);
  board.turn = b.turn;
  board.ko = b.ko;
  board.passes = b.passes;
  board.moves = b.moves;
  board.last = b.last;
  board.prisoners[1] = b.prisoners[1];
  board.prisoners[2] = b.prisoners[2];
  return board;
}

self.onmessage = (e) => {
  const job = e.data;
  current = job.id;
  if (job.type !== 'search') return;
  const S = self.Stoon.size(job.n);
  if (job.seed) S.setSeed(job.seed);
  const search = new S.Search(boardOf(S, job.board), job.komi);
  let lastShow = performance.now();
  function step() {
    if (current !== job.id) return;
    const end = performance.now() + 40;
    while (search.count < job.iters && performance.now() < end) search.run(50);
    if (search.count >= job.iters) {
      self.postMessage({ id: job.id, type: 'done', own: search.ownership(), ranked: search.ranked(), count: search.count });
      return;
    }
    const now = performance.now();
    if (job.progress && now - lastShow > 90) {
      lastShow = now;
      self.postMessage({ id: job.id, type: 'progress', own: search.ownership(), count: search.count });
    }
    // Yield so a newer job or a stop can come in.
    later(step);
  }
  step();
};
