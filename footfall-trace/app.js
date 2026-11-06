'use strict';
/* 步迹 Footfall Trace — indoor walking-path recorder for one floor.
   Pedestrian dead reckoning (step detection + Weinberg step length + gyro heading)
   fused in a particle filter constrained by the floor plan's walls, with QR anchors
   that reset position + heading and rubber-band the path recorded since the last anchor.
   Coordinates: metres, x right, y down, origin = top-left of the plan image.
   Heading: degrees clockwise from "up" on the plan. */

const DPR = Math.min(2, window.devicePixelRatio || 1);
const CELL = 0.1;            // occupancy grid cell, metres
const NPART = 400;
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => [...r.querySelectorAll(s)];
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const rad = d => d * Math.PI / 180, deg = r => r * 180 / Math.PI;
const n360 = d => ((d % 360) + 360) % 360;
const angDiff = (a, b) => { let d = n360(a - b); return d > 180 ? d - 360 : d; };
function randn() { let u = 0, v = 0; while (!u) u = Math.random(); while (!v) v = Math.random(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); }
const uid = p => p + Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
const ymd = ms => { const d = new Date(ms); return d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0'); };
const hm = ms => { const d = new Date(ms); return String(d.getHours()).padStart(2, '0') + ':' + String(d.getMinutes()).padStart(2, '0'); };
const dur = s => { s = Math.round(s); const m = Math.floor(s / 60); return m + ':' + String(s % 60).padStart(2, '0'); };
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const LS = {
  get(k, d) { try { const v = localStorage.getItem('ft.' + k); return v == null ? d : JSON.parse(v); } catch { return d; } },
  set(k, v) { try { localStorage.setItem('ft.' + k, JSON.stringify(v)); } catch { } }
};
let toastT;
function toast(msg, ms = 2600) { const t = $('#toast'); t.textContent = msg; t.classList.add('show'); clearTimeout(toastT); toastT = setTimeout(() => t.classList.remove('show'), ms); }
const css = n => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
const PALETTE = ['#e2501a', '#2a6fdb', '#2f7d55', '#9b3fb5', '#b7791f', '#0f8b8d', '#c2185b', '#5d6b2f'];

/* ---------------- IndexedDB ---------------- */
const DB = {
  db: null,
  open() {
    return new Promise((res, rej) => {
      const r = indexedDB.open('footfall-trace', 1);
      r.onupgradeneeded = () => { const d = r.result; d.createObjectStore('floors', { keyPath: 'id' }); d.createObjectStore('sessions', { keyPath: 'id' }); };
      r.onsuccess = () => { this.db = r.result; res(); };
      r.onerror = () => rej(r.error);
    });
  },
  tx(store, mode, fn) {
    return new Promise((res, rej) => {
      const t = this.db.transaction(store, mode); const req = fn(t.objectStore(store));
      t.oncomplete = () => res(req ? req.result : undefined); t.onerror = () => rej(t.error);
    });
  },
  put(s, v) { return this.tx(s, 'readwrite', o => o.put(v)); },
  get(s, k) { return this.tx(s, 'readonly', o => o.get(k)); },
  all(s) { return this.tx(s, 'readonly', o => o.getAll()); },
  del(s, k) { return this.tx(s, 'readwrite', o => o.delete(k)); }
};

/* ---------------- Floor runtime ---------------- */
let floor = null;           // persisted floor object
let img = null;             // HTMLImageElement
let gw = 0, gh = 0, imgLum = null, wall = null, wallCanvas = null;

function loadImage(src) { return new Promise((res, rej) => { const i = new Image(); i.onload = () => res(i); i.onerror = rej; i.src = src; }); }
function floorWH() { return { W: floor.imgW / floor.pxPerM, H: floor.imgH / floor.pxPerM }; }

function rebuildImageGrid() {
  const { W, H } = floorWH();
  gw = Math.ceil(W / CELL); gh = Math.ceil(H / CELL);
  const c = document.createElement('canvas'); c.width = floor.imgW; c.height = floor.imgH;
  const x = c.getContext('2d', { willReadFrequently: true });
  x.fillStyle = '#fff'; x.fillRect(0, 0, c.width, c.height); x.drawImage(img, 0, 0, c.width, c.height);
  const d = x.getImageData(0, 0, c.width, c.height).data;
  imgLum = new Uint8Array(gw * gh).fill(255);
  const cpx = CELL * floor.pxPerM;
  if (cpx >= 1) {
    for (let py = 0; py < c.height; py++) {
      const cy = Math.min(gh - 1, Math.floor(py / cpx));
      for (let px = 0; px < c.width; px++) {
        const k = (py * c.width + px) * 4; const l = (d[k] * 299 + d[k + 1] * 587 + d[k + 2] * 114) / 1000;
        const i = cy * gw + Math.min(gw - 1, Math.floor(px / cpx)); if (l < imgLum[i]) imgLum[i] = l;
      }
    }
  } else {
    for (let cy = 0; cy < gh; cy++) for (let cx = 0; cx < gw; cx++) {
      const px = Math.min(c.width - 1, Math.floor((cx + .5) * cpx)), py = Math.min(c.height - 1, Math.floor((cy + .5) * cpx));
      const k = (py * c.width + px) * 4; imgLum[cy * gw + cx] = (d[k] * 299 + d[k + 1] * 587 + d[k + 2] * 114) / 1000;
    }
  }
  if (!(floor.overrides instanceof Uint8Array) || floor.overrides.length !== gw * gh || floor.gw !== gw) { floor.overrides = new Uint8Array(gw * gh); floor.gw = gw; floor.gh = gh; }
  rebuildWalls();
}
function rebuildWalls() {
  wall = new Uint8Array(gw * gh);
  const ov = floor.overrides, thr = floor.threshold, use = floor.useImageWalls;
  if (!wallCanvas) wallCanvas = document.createElement('canvas');
  wallCanvas.width = gw; wallCanvas.height = gh;
  const wx = wallCanvas.getContext('2d'); const id = wx.createImageData(gw, gh); const p = id.data;
  for (let i = 0; i < gw * gh; i++) {
    const o = ov[i]; const w = o === 1 ? 1 : o === 2 ? 0 : (use && imgLum[i] < thr ? 1 : 0); wall[i] = w;
    if (w) { p[i * 4] = 226; p[i * 4 + 1] = 80; p[i * 4 + 2] = 26; p[i * 4 + 3] = o === 1 ? 210 : 150; }
    else if (o === 2) { p[i * 4] = 47; p[i * 4 + 1] = 160; p[i * 4 + 2] = 90; p[i * 4 + 3] = 110; }
  }
  wx.putImageData(id, 0, 0);
}
function isWallAt(x, y) {
  const cx = Math.floor(x / CELL), cy = Math.floor(y / CELL);
  if (cx < 0 || cy < 0 || cx >= gw || cy >= gh) return true;
  return wall[cy * gw + cx] === 1;
}
function segBlocked(x0, y0, x1, y1) {
  const n = Math.max(1, Math.ceil(Math.hypot(x1 - x0, y1 - y0) / 0.05));
  for (let i = 1; i <= n; i++) { const t = i / n; if (isWallAt(x0 + (x1 - x0) * t, y0 + (y1 - y0) * t)) return true; }
  return false;
}
function nearestWallDir(x, y, R = 2.5) {
  let best = null, bd = 1e9; const r = Math.ceil(R / CELL), cx0 = Math.floor(x / CELL), cy0 = Math.floor(y / CELL);
  for (let dy = -r; dy <= r; dy++) for (let dx = -r; dx <= r; dx++) {
    const cx = cx0 + dx, cy = cy0 + dy; if (cx < 0 || cy < 0 || cx >= gw || cy >= gh || !wall[cy * gw + cx]) continue;
    const d = dx * dx + dy * dy; if (d < bd && d > 0) { bd = d; best = [dx, dy]; }
  }
  return best ? n360(deg(Math.atan2(best[0], -best[1]))) : null;
}
function rle(a) { const out = []; let v = a[0], n = 0; for (let i = 0; i < a.length; i++) { if (a[i] === v) n++; else { out.push(v, n); v = a[i]; n = 1; } } out.push(v, n); return out; }
function unrle(r, len) { const a = new Uint8Array(len); let k = 0; for (let i = 0; i < r.length; i += 2) { a.fill(r[i], k, k + r[i + 1]); k += r[i + 1]; } return a; }

async function setFloor(f, { fit = true } = {}) {
  floor = f; img = await loadImage(f.image);
  rebuildImageGrid();
  LS.set('floorId', f.id);
  $('#hdrFloor').textContent = f.name;
  if (fit) fitView();
  refreshSetup(); refreshFloorSel(); refreshCalPairs(); renderLib(); draw();
}
async function saveFloor() { if (floor) await DB.put('floors', floor); }

/* ---------------- Sample floor (fictional studio floor, 30 × 20 m) ---------------- */
async function makeSampleFloor() {
  const S = 30, W = 30, H = 20; const c = document.createElement('canvas'); c.width = W * S; c.height = H * S; const x = c.getContext('2d');
  x.fillStyle = '#fbfaf7'; x.fillRect(0, 0, c.width, c.height);
  x.fillStyle = '#bdb7ab'; x.font = `${0.7 * S}px sans-serif`; x.textAlign = 'center';
  [['Studio A', 7, 1.6], ['Studio B', 18, 1.6], ['Crit Room', 25.8, 1.6], ['Corridor', 20, 10], ['Workshop', 5.3, 19], ['Open Studio', 17, 12.2], ['Stairs / Lift', 26.8, 15.5]].forEach(([t, a, b]) => x.fillText(t, a * S, b * S));
  x.strokeStyle = '#1e1d1a'; x.lineCap = 'butt';
  const L = (pts, w = 0.25) => { x.lineWidth = w * S; x.beginPath(); pts.forEach(([a, b], i) => i ? x.lineTo(a * S, b * S) : x.moveTo(a * S, b * S)); x.stroke(); };
  // outer walls (west entrance gap at corridor y 8.6–10.4)
  L([[0.5, 8.6], [0.5, 0.5], [29.5, 0.5], [29.5, 19.5], [0.5, 19.5], [0.5, 10.4]], 0.35);
  // corridor north wall y=8, doors at 6–7.2, 17–18.2, 25–26.2
  L([[0.5, 8], [6, 8]]); L([[7.2, 8], [17, 8]]); L([[18.2, 8], [25, 8]]); L([[26.2, 8], [29.5, 8]]);
  // corridor south wall y=11, doors 4–5.4, 15–17, 26–27.2
  L([[0.5, 11], [4, 11]]); L([[5.4, 11], [15, 11]]); L([[17, 11], [26, 11]]); L([[27.2, 11], [29.5, 11]]);
  L([[14, 0.5], [14, 8]]); L([[22, 0.5], [22, 8]]); L([[10, 11], [10, 19.5]]); L([[24, 11], [24, 19.5]]);
  // stair core
  x.lineWidth = 0.06 * S; for (let i = 0; i < 9; i++) { x.beginPath(); x.moveTo(25 * S, (12.5 + i * 0.35) * S); x.lineTo(28.8 * S, (12.5 + i * 0.35) * S); x.stroke(); }
  x.fillStyle = '#1e1d1a'; x.fillRect(25 * S, 12.3 * S, 3.8 * S, 0.12 * S); x.fillRect(25 * S, 15.6 * S, 3.8 * S, 0.12 * S);
  // furniture (drawn dark = obstacle)
  x.fillStyle = '#5f5a50';
  const R = (a, b, w, h) => x.fillRect(a * S, b * S, w * S, h * S);
  R(2, 2.5, 4, 1.2); R(8.2, 2.5, 4, 1.2); R(2, 5.3, 4, 1.2); R(8.2, 5.3, 4, 1.2);       // Studio A desks
  R(15.5, 3, 5, 1.2); R(15.5, 5.6, 5, 1.0);                                               // Studio B
  R(24.5, 3.6, 3, 1.4);                                                                   // crit table
  R(2, 13, 6, 1.2); R(2, 16.4, 6, 1.2);                                                   // workshop benches
  R(11.5, 13.4, 3.5, 1); R(17.5, 13.4, 5, 1); R(11.5, 16.6, 3.5, 1); R(17.5, 16.6, 5, 1); // open studio
  R(6.9, 4.2, 0.5, 0.5); R(16.2, 15.2, 0.5, 0.5);                                         // columns
  const image = c.toDataURL('image/png');
  return {
    id: 'sample-studio', name: '示例：工作室楼层（虚构）', image, imgW: c.width, imgH: c.height, pxPerM: S,
    threshold: 110, useImageWalls: true, overrides: null,
    anchors: [
      { id: 'A1', label: '西入口', x: 1.3, y: 9.5, face: 270, type: 'normal' },
      { id: 'A2', label: '走廊中段', x: 12, y: 8.6, face: 0, type: 'normal' },
      { id: 'A3', label: 'Studio A', x: 1.2, y: 4.3, face: 270, type: 'normal' },
      { id: 'A4', label: 'Open Studio', x: 17, y: 18.8, face: 180, type: 'normal' },
      { id: 'A5', label: 'Crit Room', x: 28.8, y: 6.5, face: 90, type: 'normal' },
      { id: 'A6', label: 'Workshop', x: 9.3, y: 15, face: 90, type: 'normal' },
      { id: 'E1', label: '楼梯口', x: 26.6, y: 10.4, face: 180, type: 'exit' }
    ],
    createdAt: Date.now()
  };
}

/* ---------------- View / drawing ---------------- */
const cv = $('#map'), ctx = cv.getContext('2d');
const view = { s: 20, ox: 0, oy: 0 };
let userMoved = false;
function resize() { const r = cv.getBoundingClientRect(); cv.width = Math.max(1, r.width * DPR); cv.height = Math.max(1, r.height * DPR); if (!userMoved) fitView(); else draw(); }
function fitView() {
  if (!floor) return; const { W, H } = floorWH(); const r = cv.getBoundingClientRect(); const w = r.width * DPR, h = r.height * DPR;
  view.s = Math.min(w / W, h / H) * 0.94; view.ox = (w - W * view.s) / 2; view.oy = (h - H * view.s) / 2; draw();
}
function zoomAt(f, sx, sy) { userMoved = true; const mx = (sx - view.ox) / view.s, my = (sy - view.oy) / view.s; view.s = clamp(view.s * f, 2, 600); view.ox = sx - mx * view.s; view.oy = sy - my * view.s; draw(); }
const toMap = (cx, cy) => { const r = cv.getBoundingClientRect(); return [((cx - r.left) * DPR - view.ox) / view.s, ((cy - r.top) * DPR - view.oy) / view.s]; };
const px = n => n * DPR / view.s;

let drawQueued = false;
function draw() { if (!drawQueued) { drawQueued = true; requestAnimationFrame(() => { drawQueued = false; render(); }); } }
function render() {
  ctx.setTransform(1, 0, 0, 1, 0, 0); ctx.fillStyle = css('--sheet'); ctx.fillRect(0, 0, cv.width, cv.height);
  if (!floor) return;
  const { W, H } = floorWH();
  ctx.setTransform(view.s, 0, 0, view.s, view.ox, view.oy);
  const dark = css('--paper') < '#5';
  ctx.globalAlpha = dark ? 0.82 : 1; ctx.drawImage(img, 0, 0, W, H); ctx.globalAlpha = 1;
  if (tab === 'setup' || showWallsAlways) { ctx.imageSmoothingEnabled = false; ctx.globalAlpha = tab === 'setup' ? 0.75 : 0.35; ctx.drawImage(wallCanvas, 0, 0, gw * CELL, gh * CELL); ctx.globalAlpha = 1; ctx.imageSmoothingEnabled = true; }
  ctx.strokeStyle = css('--hair'); ctx.lineWidth = px(1); ctx.strokeRect(0, 0, W, H);
  // scale bar
  drawScaleBar(W, H);
  if (tab === 'lib') drawLibrary();
  if (tab === 'rec' || tab === 'cal') drawLive();
  drawAnchors();
  if (tab === 'setup' && mode === 'scale') { ctx.fillStyle = css('--signal'); scalePts.forEach(p => { ctx.beginPath(); ctx.arc(p[0], p[1], px(6), 0, 7); ctx.fill(); }); if (scalePts.length === 2) { ctx.strokeStyle = css('--signal'); ctx.lineWidth = px(2); ctx.beginPath(); ctx.moveTo(...scalePts[0]); ctx.lineTo(...scalePts[1]); ctx.stroke(); } }
  if (tab === 'rec' && !live && simPts.length) {
    ctx.strokeStyle = css('--ink-2'); ctx.setLineDash([px(6), px(5)]); ctx.lineWidth = px(1.5); ctx.beginPath(); simPts.forEach((p, i) => i ? ctx.lineTo(p[0], p[1]) : ctx.moveTo(p[0], p[1])); ctx.stroke(); ctx.setLineDash([]);
    ctx.fillStyle = css('--ink'); simPts.forEach(p => { ctx.beginPath(); ctx.arc(p[0], p[1], px(3.5), 0, 7); ctx.fill(); });
  }
  if (brushCursor && (mode === 'wall' || mode === 'erase')) { ctx.strokeStyle = css('--ink'); ctx.lineWidth = px(1); ctx.beginPath(); ctx.arc(brushCursor[0], brushCursor[1], brushR, 0, 7); ctx.stroke(); }
}
function drawScaleBar(W, H) {
  const target = 120 * DPR / view.s; const steps = [0.5, 1, 2, 5, 10, 20, 50]; const m = steps.find(s => s >= target / 2) || 50;
  const x0 = 0.3, y0 = H + px(18); ctx.strokeStyle = css('--ink'); ctx.lineWidth = px(2); ctx.beginPath(); ctx.moveTo(x0, y0); ctx.lineTo(x0 + m, y0); ctx.stroke();
  ctx.fillStyle = css('--ink-2'); ctx.font = `${px(10)}px IBM Plex Mono, monospace`; ctx.fillText(m + ' m', x0 + m + px(5), y0 + px(3.5));
}
function drawAnchors() {
  const sel = tab === 'setup' ? selAnchor : (pickTarget && pickTarget.id);
  for (const a of floor.anchors) {
    const r = px(7); const exit = a.type === 'exit';
    if (a.face != null) { const h = rad(a.face); ctx.strokeStyle = css('--ink'); ctx.lineWidth = px(1.5); ctx.beginPath(); ctx.moveTo(a.x, a.y); const ex = a.x + Math.sin(h) * px(18), ey = a.y - Math.cos(h) * px(18); ctx.lineTo(ex, ey); ctx.stroke(); ctx.beginPath(); ctx.moveTo(ex, ey); ctx.lineTo(ex - Math.sin(h - 0.5) * px(6), ey + Math.cos(h - 0.5) * px(6)); ctx.lineTo(ex - Math.sin(h + 0.5) * px(6), ey + Math.cos(h + 0.5) * px(6)); ctx.closePath(); ctx.fillStyle = css('--ink'); ctx.fill(); }
    ctx.fillStyle = exit ? css('--signal') : css('--ink'); ctx.beginPath();
    if (exit) ctx.rect(a.x - r, a.y - r, 2 * r, 2 * r); else { ctx.moveTo(a.x, a.y - r * 1.2); ctx.lineTo(a.x + r * 1.2, a.y); ctx.lineTo(a.x, a.y + r * 1.2); ctx.lineTo(a.x - r * 1.2, a.y); ctx.closePath(); }
    ctx.fill();
    if (a.id === sel) { ctx.strokeStyle = css('--signal'); ctx.lineWidth = px(2.5); ctx.beginPath(); ctx.arc(a.x, a.y, px(13), 0, 7); ctx.stroke(); }
    ctx.fillStyle = css('--ink'); ctx.font = `500 ${px(10.5)}px IBM Plex Mono, monospace`; ctx.fillText(a.id, a.x + px(10), a.y - px(8));
  }
}
function polyline(pts, color, w, dash) {
  if (pts.length < 2) return; ctx.strokeStyle = color; ctx.lineWidth = px(w); ctx.lineJoin = 'round'; ctx.lineCap = 'round'; ctx.setLineDash(dash || []);
  ctx.beginPath(); ctx.moveTo(pts[0].x, pts[0].y); for (let i = 1; i < pts.length; i++) ctx.lineTo(pts[i].x, pts[i].y); ctx.stroke(); ctx.setLineDash([]);
}
function drawBG() {
  const m = (p, col) => { ctx.fillStyle = col; ctx.beginPath(); ctx.arc(p.x, p.y, px(7), 0, 7); ctx.fill(); };
  if (BG.start) { m(BG.start, css('--ok')); if (BG.start.face != null) { const h = rad(BG.start.face); ctx.strokeStyle = css('--ok'); ctx.lineWidth = px(3); ctx.beginPath(); ctx.moveTo(BG.start.x, BG.start.y); ctx.lineTo(BG.start.x + Math.sin(h) * px(40), BG.start.y - Math.cos(h) * px(40)); ctx.stroke(); } }
}
function drawLive() {
  if (!live) drawBG();
  if (pickMode && pickTarget && pickTarget.custom) { const t = pickTarget; ctx.fillStyle = css('--signal'); ctx.beginPath(); ctx.arc(t.x, t.y, px(7), 0, 7); ctx.fill(); if (t.face != null) { const h = rad(t.face); ctx.strokeStyle = css('--signal'); ctx.lineWidth = px(3); ctx.beginPath(); ctx.moveTo(t.x, t.y); ctx.lineTo(t.x + Math.sin(h) * px(40), t.y - Math.cos(h) * px(40)); ctx.stroke(); } }
  if (simTruth.length) polyline(simTruth, css('--muted'), 1.2, [px(3), px(4)]);
  if (!live) return;
  if (live.path.length) {
    polyline(correctedPath(live), css('--signal'), 3);
  }
  if (tracker.p.length && $('#showParticles').checked) { ctx.fillStyle = css('--ink-2'); ctx.globalAlpha = 0.45; const r = px(1.4); for (const p of tracker.p) ctx.fillRect(p.x - r, p.y - r, 2 * r, 2 * r); ctx.globalAlpha = 1; }
  const e = tracker.last; if (e && liveState === 'tracking') {
    ctx.fillStyle = css('--signal'); ctx.globalAlpha = 0.15; ctx.beginPath(); ctx.arc(e.x, e.y, Math.max(e.sd, 0.2), 0, 7); ctx.fill(); ctx.globalAlpha = 1;
    const y = Sensors.sim ? simYaw : Sensors.yawNow(); if (y != null) { const h = rad(y + live.offset); ctx.strokeStyle = css('--ink'); ctx.lineWidth = px(2); ctx.beginPath(); ctx.moveTo(e.x, e.y); ctx.lineTo(e.x + Math.sin(h) * px(22), e.y - Math.cos(h) * px(22)); ctx.stroke(); }
    ctx.fillStyle = css('--ink'); ctx.beginPath(); ctx.arc(e.x, e.y, px(5), 0, 7); ctx.fill(); ctx.strokeStyle = css('--sheet'); ctx.lineWidth = px(1.5); ctx.stroke();
  }
}

/* ---------------- Pointer interaction ---------------- */
const pointers = new Map(); let gesture = null; let brushCursor = null; const brushR = 0.35;
cv.addEventListener('pointerdown', e => {
  cv.setPointerCapture(e.pointerId); pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (pointers.size === 1) { gesture = { x: e.clientX, y: e.clientY, moved: false, ox: view.ox, oy: view.oy }; if (mode === 'wall' || mode === 'erase') paint(e); }
  else if (pointers.size === 2) { const [a, b] = [...pointers.values()]; gesture = { pinch: true, d: Math.hypot(a.x - b.x, a.y - b.y), mx: (a.x + b.x) / 2, my: (a.y + b.y) / 2, moved: true }; }
});
cv.addEventListener('pointermove', e => {
  if (mode === 'wall' || mode === 'erase') { brushCursor = toMap(e.clientX, e.clientY); draw(); }
  if (!pointers.has(e.pointerId)) return; pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (!gesture) return;
  if (gesture.pinch && pointers.size >= 2) {
    const [a, b] = [...pointers.values()]; const d = Math.hypot(a.x - b.x, a.y - b.y), mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
    const r = cv.getBoundingClientRect(); view.ox += (mx - gesture.mx) * DPR; view.oy += (my - gesture.my) * DPR;
    zoomAt(d / gesture.d, (mx - r.left) * DPR, (my - r.top) * DPR); gesture.d = d; gesture.mx = mx; gesture.my = my; return;
  }
  if (Math.hypot(e.clientX - gesture.x, e.clientY - gesture.y) > 6) gesture.moved = true;
  if (mode === 'wall' || mode === 'erase') { paint(e); return; }
  if (gesture.moved) { userMoved = true; view.ox = gesture.ox + (e.clientX - gesture.x) * DPR; view.oy = gesture.oy + (e.clientY - gesture.y) * DPR; draw(); }
});
function endPointer(e) {
  pointers.delete(e.pointerId);
  if (gesture && !gesture.pinch && !gesture.moved && pointers.size === 0 && e.type === 'pointerup') onTap(...toMap(e.clientX, e.clientY));
  if (pointers.size === 0) { if (gesture && (mode === 'wall' || mode === 'erase')) saveFloor(); gesture = null; }
}
cv.addEventListener('pointerup', endPointer); cv.addEventListener('pointercancel', endPointer);
cv.addEventListener('pointerleave', () => { brushCursor = null; draw(); });
cv.addEventListener('wheel', e => { e.preventDefault(); const r = cv.getBoundingClientRect(); zoomAt(Math.exp(-e.deltaY * 0.0015), (e.clientX - r.left) * DPR, (e.clientY - r.top) * DPR); }, { passive: false });
$('#zoomIn').onclick = () => zoomAt(1.4, cv.width / 2, cv.height / 2);
$('#zoomOut').onclick = () => zoomAt(1 / 1.4, cv.width / 2, cv.height / 2);
$('#zoomFit').onclick = () => { userMoved = false; fitView(); };
function paint(e) {
  const [mx, my] = toMap(e.clientX, e.clientY); brushCursor = [mx, my]; const v = mode === 'wall' ? 1 : 2; const r = Math.ceil(brushR / CELL);
  const cx0 = Math.floor(mx / CELL), cy0 = Math.floor(my / CELL);
  for (let dy = -r; dy <= r; dy++) for (let dx = -r; dx <= r; dx++) { if (dx * dx + dy * dy > r * r) continue; const cx = cx0 + dx, cy = cy0 + dy; if (cx < 0 || cy < 0 || cx >= gw || cy >= gh) continue; floor.overrides[cy * gw + cx] = v; }
  rebuildWalls(); draw();
}
function anchorNear(x, y, R = 1.5) { let best = null, bd = R; for (const a of floor.anchors) { const d = Math.hypot(a.x - x, a.y - y); if (d < bd) { bd = d; best = a; } } return best; }
function onTap(x, y) {
  if (tab === 'setup') {
    if (mode === 'scale') { scalePts.push([x, y]); if (scalePts.length > 2) scalePts = [[x, y]]; $('#scaleRow').hidden = scalePts.length !== 2; if (scalePts.length === 2) $('#scaleDist').focus(); draw(); }
    else if (mode === 'anchor') {
      const a = anchorNear(x, y, px(18) + 0.3);
      if (a) selAnchor = a.id;
      else {
        let n = 1; while (floor.anchors.some(q => q.id === 'A' + n)) n++;
        const na = { id: 'A' + n, label: '', x: +x.toFixed(2), y: +y.toFixed(2), face: nearestWallDir(x, y), type: 'normal' };
        floor.anchors.push(na); selAnchor = na.id; saveFloor(); refreshCalPairs();
      }
      refreshAnchorEd(); draw();
    }
  } else if (tab === 'rec') {
    if (mode === 'bgStart') { bgTap(x, y); return; }
    if (live && pickMode) {
      if (pickTarget && pickTarget.custom && pickTarget.face == null) {
        if (Math.hypot(x - pickTarget.x, y - pickTarget.y) < 0.3) return;
        pickTarget.face = n360(deg(Math.atan2(x - pickTarget.x, -(y - pickTarget.y)))); $('#pickOk').disabled = false;
        $('#pickMsg').textContent = '按箭头方向站好，手机顶端朝前，然后点“确认在此”。';
      } else {
        const a = anchorNear(x, y, 1.0);
        if (a) { pickTarget = a; $('#pickOk').disabled = false; $('#pickMsg').textContent = `面朝 ${a.id}${a.label ? '（' + a.label + '）' : ''} 的二维码站好，再点“确认在此”。`; }
        else if (isWallAt(x, y)) { toast('这里是墙，点在可以站的地方'); return; }
        else { pickTarget = { id: '手动', label: '', x: +x.toFixed(2), y: +y.toFixed(2), face: null, type: 'normal', custom: true }; $('#pickOk').disabled = true; $('#pickMsg').textContent = '再点一下你面朝的方向（往前几米的地方）。'; }
      }
      draw();
    }
    else if (!live) { simPts.push([x, y]); simTruth = []; draw(); }
  }
}

/* ---------------- Sensors: step detection + heading ---------------- */
const Sensors = {
  on: false, sim: false, lastMotion: 0, hist: [], onStep: null, compass: null, count: 0,
  g: [0, 0, 9.81], lp: 0, st: 0, peak: 0, peakT: 0, trough: 0, lastStepT: 0, avgPeak: 2,
  async start() {
    if (this.on) return;
    if (!window.isSecureContext) throw new Error('需要用 https:// 链接打开，传感器才能用。');
    if (typeof DeviceMotionEvent === 'undefined') throw new Error('这个浏览器没有运动传感器（电脑上可以用演示模式）。');
    const asks = [];
    if (typeof DeviceMotionEvent.requestPermission === 'function') asks.push(DeviceMotionEvent.requestPermission());
    if (typeof DeviceOrientationEvent !== 'undefined' && typeof DeviceOrientationEvent.requestPermission === 'function') asks.push(DeviceOrientationEvent.requestPermission());
    const res = await Promise.all(asks.map(p => p.catch(() => 'denied')));
    if (res.some(r => r !== 'granted')) throw new Error('没有拿到“运动与方向”权限。iPhone：设置 → Safari → 高级 → 网站数据里清掉这个网站后重新打开，再点允许。');
    addEventListener('devicemotion', e => this.motion(e));
    addEventListener('deviceorientation', e => this.orient(e));
    this.on = true;
    await new Promise(r => setTimeout(r, 1200));
    if (!this.lastMotion) { this.on = false; throw new Error('收不到传感器数据。请在手机上打开（电脑上可以用演示模式）。'); }
  },
  motion(e) {
    const a = e.accelerationIncludingGravity; if (!a || a.x == null) return;
    const t = performance.now(); this.lastMotion = t;
    const g = this.g, k = 0.04; g[0] += k * (a.x - g[0]); g[1] += k * (a.y - g[1]); g[2] += k * (a.z - g[2]);
    const gn = Math.hypot(g[0], g[1], g[2]) || 9.81;
    const vert = ((a.x - g[0]) * g[0] + (a.y - g[1]) * g[1] + (a.z - g[2]) * g[2]) / gn;
    this.lp += 0.3 * (vert - this.lp); const v = this.lp;
    const thr = clamp(0.4 * this.avgPeak, 0.6, 2.2);
    if (this.st === 0) { if (v < this.trough) this.trough = v; if (v > thr) { this.st = 1; this.peak = v; this.peakT = t; } }
    else {
      if (v > this.peak) { this.peak = v; this.peakT = t; }
      if (v < 0) {
        const dt = this.peakT - this.lastStepT;
        if (dt > 280) { const amp = this.peak - Math.min(this.trough, 0); this.avgPeak = 0.8 * this.avgPeak + 0.2 * this.peak; this.lastStepT = this.peakT; this.count++; this.onStep && this.onStep({ amp, yaw: this.yawNow() }); }
        this.st = 0; this.trough = v;
      }
    }
  },
  orient(e) {
    if (e.alpha == null) return;
    const A = rad(e.alpha), B = rad(e.beta || 0), G = rad(e.gamma || 0);
    const cA = Math.cos(A), sA = Math.sin(A), cB = Math.cos(B), sB = Math.sin(B), cG = Math.cos(G), sG = Math.sin(G);
    // phone "forward" = top edge (y axis) when flat, back camera (-z) when upright; use y − z projected on the floor
    const vx = -cB * sA - (cG * sA * sB + cA * sG), vy = cA * cB - (sA * sG - cA * cG * sB);
    if (Math.hypot(vx, vy) < 0.2) return;
    const h = deg(Math.atan2(vx, vy)); const t = performance.now();
    this.hist.push([t, Math.sin(rad(h)), Math.cos(rad(h))]); while (this.hist.length && t - this.hist[0][0] > 1000) this.hist.shift();
    if (e.webkitCompassHeading != null) this.compass = e.webkitCompassHeading;
  },
  yawNow() {
    const t = performance.now(); let s = 0, c = 0; for (const [ti, si, ci] of this.hist) if (t - ti < 350) { s += si; c += ci; }
    if (!s && !c) { const l = this.hist[this.hist.length - 1]; if (!l) return null; s = l[1]; c = l[2]; }
    return n360(deg(Math.atan2(s, c)));
  }
};
let wakeLock = null;
async function keepAwake() { try { wakeLock = await navigator.wakeLock?.request('screen'); } catch { } }
function releaseAwake() { try { wakeLock?.release(); } catch { } wakeLock = null; }

/* ---------------- Particle filter ---------------- */
const tracker = {
  p: [], last: null, recoveries: 0, constrain: true,
  init(x, y, sig) {
    this.p = [];
    for (let i = 0; i < NPART; i++) {
      let px = x, py = y; for (let k = 0; k < 20; k++) { px = x + randn() * sig; py = y + randn() * sig; if (!isWallAt(px, py)) break; }
      if (isWallAt(px, py)) { px = x; py = y; }
      this.p.push({ x: px, y: py, hb: randn() * 5, s: 1 + randn() * 0.07, w: 1 / NPART });
    }
    this.estimate();
  },
  step(len, h) {
    let alive = 0, killed = 0;
    for (const p of this.p) {
      if (p.w === 0) continue;
      const hh = rad(h + p.hb + randn() * 6), L = Math.max(0.1, len * p.s + randn() * 0.05);
      const nx = p.x + L * Math.sin(hh), ny = p.y - L * Math.cos(hh);
      if (this.constrain && segBlocked(p.x, p.y, nx, ny)) { p.w = 0; killed++; } else { p.x = nx; p.y = ny; alive++; }
      p.hb += randn() * 0.4; p.s = clamp(p.s + randn() * 0.004, 0.75, 1.3);
    }
    this.lastKilled = killed;
    if (!alive) { // every candidate hit a wall: re-seed around the last estimate pushed one step forward
      this.recoveries++; const e = this.last; const hh = rad(h);
      this.init(e.x + len * Math.sin(hh), e.y - len * Math.cos(hh), 0.8); return false;
    }
    let sw = 0; for (const p of this.p) sw += p.w; let s2 = 0; for (const p of this.p) { p.w /= sw; s2 += p.w * p.w; }
    if (1 / s2 < NPART / 2) this.resample();
    this.estimate(); return true;
  },
  resample() {
    const n = this.p.length, out = []; const u0 = Math.random() / n; let c = this.p[0].w, i = 0;
    for (let j = 0; j < n; j++) { const u = u0 + j / n; while (u > c && i < n - 1) { i++; c += this.p[i].w; } const q = this.p[i]; out.push({ x: q.x, y: q.y, hb: q.hb, s: q.s, w: 1 / n }); }
    this.p = out;
  },
  estimate() {
    let x = 0, y = 0; for (const p of this.p) { x += p.w * p.x; y += p.w * p.y; }
    let v = 0; for (const p of this.p) v += p.w * ((p.x - x) ** 2 + (p.y - y) ** 2);
    if (isWallAt(x, y)) { let best = this.p[0], bd = 1e9; for (const p of this.p) { const d = (p.x - x) ** 2 + (p.y - y) ** 2; if (d < bd) { bd = d; best = p; } } x = best.x; y = best.y; }
    this.last = { x, y, sd: Math.sqrt(v) }; return this.last;
  }
};

/* ---------------- Profiles ---------------- */
const DEFAULT_K = 0.47;
let profiles = LS.get('profiles', null);
if (!profiles || !profiles.length) profiles = [{ id: uid('p'), name: '我', K: DEFAULT_K, calibrated: false }];
let curProfile = LS.get('profile', profiles[0].id);
const prof = () => profiles.find(p => p.id === curProfile) || profiles[0];
function saveProfiles() { LS.set('profiles', profiles); LS.set('profile', curProfile); refreshProfiles(); }
function refreshProfiles() {
  const opts = profiles.map(p => `<option value="${p.id}"${p.id === prof().id ? ' selected' : ''}>${esc(p.name)}</option>`).join('');
  $('#recWho').innerHTML = opts; $('#calWho').innerHTML = opts;
  const p = prof(); const typ = (p.K * Math.pow(3.2, 0.25)).toFixed(2);
  $('#recK').innerHTML = p.calibrated ? `步长系数 ${p.K.toFixed(3)} · 约 ${typ} m/步` : `<span class="pill warn">未校准</span> 先去“步长校准”走一次 10 米`;
  $('#calInfo').innerHTML = p.calibrated ? `步长系数 K = <b class="mono">${p.K.toFixed(3)}</b>（正常步速约 ${typ} m/步）· 校准 ${p.calN || 1} 次` : `还没校准，用默认值 K = ${DEFAULT_K}。`;
}
$('#recWho').onchange = e => { curProfile = e.target.value; saveProfiles(); };
$('#calWho').onchange = e => { curProfile = e.target.value; saveProfiles(); };
$('#calNew').onclick = () => { $('#calRenRow').hidden = false; $('#calName').value = ''; $('#calName').dataset.mode = 'new'; $('#calName').focus(); };
$('#calRen').onclick = () => { $('#calRenRow').hidden = false; $('#calName').value = prof().name; $('#calName').dataset.mode = 'ren'; $('#calName').focus(); };
$('#calSave').onclick = () => {
  const n = $('#calName').value.trim(); if (!n) return toast('写个名字');
  if ($('#calName').dataset.mode === 'new') { const p = { id: uid('p'), name: n, K: DEFAULT_K, calibrated: false }; profiles.push(p); curProfile = p.id; } else prof().name = n;
  $('#calRenRow').hidden = true; saveProfiles();
};

/* ---------------- Recording ---------------- */
let live = null, liveState = 'idle', pickMode = false, pickTarget = null, simPts = [], simTruth = [], simYaw = 0, showWallsAlways = false;
let saveTick = 0, hiddenAt = 0;
const clock = () => Sensors.sim ? simClock : Date.now();
let simClock = 0;

function newSession(sim) {
  const p = prof(); const t = clock();
  return { id: uid('s'), format: 'footfall-trace/v1', floorId: floor.id, floorName: floor.name, participant: p.name, participantId: p.id, K: p.K, calibrated: !!p.calibrated,
    sim: !!sim, date: ymd(t), startedAt: t, endedAt: null, offset: 0, steps: [], path: [], anchors: [], gaps: [], recoveries: 0, device: navigator.userAgent };
}
async function startRecording() {
  if (!floor) return toast('先在地图设置里准备平面图');
  try { await Sensors.start(); } catch (err) { return toast(err.message, 6000); }
  Sensors.sim = false; keepAwake();
  live = newSession(false); liveState = 'needsAnchor'; tracker.constrain = true; simTruth = [];
  Sensors.onStep = s => onStep(s);
  showLive(); $('#btnPick').click(); updateLive(); draw();
}
function onStep({ amp, yaw }) {
  if (!live || liveState !== 'tracking' || yaw == null) return;
  const len = clamp(live.K * Math.pow(Math.max(amp, 0.05), 0.25), 0.25, 1.15);
  const h = n360(yaw + live.offset);
  tracker.step(len, h); const e = tracker.last; const t = clock();
  live.steps.push({ t, len: +len.toFixed(3), amp: +amp.toFixed(2), yaw: +yaw.toFixed(1), h: +h.toFixed(1) });
  live.path.push({ t, x: +e.x.toFixed(3), y: +e.y.toFixed(3), sd: +e.sd.toFixed(2) });
  live.recoveries = tracker.recoveries;
  if (++saveTick % 10 === 0) DB.put('sessions', live).catch(() => { });
  updateLive(); draw();
}
function fixAnchor(a, align, yawAtScan) {
  if (!live) return;
  const t = clock(); const yaw = yawAtScan ?? (Sensors.sim ? null : Sensors.yawNow());
  let headingCorr = null;
  if (align && yaw != null && a.face != null) { const no = n360(a.face - yaw); headingCorr = live.anchors.length ? angDiff(no, live.offset) : null; live.offset = no; }
  const wasTracking = liveState === 'tracking'; const e = tracker.last;
  live.anchors.push({ t, id: a.id, x: a.x, y: a.y, pathIndex: live.path.length, estX: wasTracking ? +e.x.toFixed(3) : null, estY: wasTracking ? +e.y.toFixed(3) : null, err: wasTracking ? +Math.hypot(e.x - a.x, e.y - a.y).toFixed(2) : null, headingCorr: headingCorr == null ? null : +headingCorr.toFixed(1) });
  live.path.push({ t, x: a.x, y: a.y, sd: 0.3, anchor: a.id });
  tracker.init(a.x, a.y, 0.3); liveState = 'tracking';
  DB.put('sessions', live).catch(() => { });
  if (!Sensors.sim) toast(wasTracking ? `已在 ${a.id} 校正（偏差 ${live.anchors.at(-1).err} m）` : `开始了，正常走吧`);
  if (a.type === 'exit' && wasTracking) { endRecording('出口'); return; }
  updateLive(); draw();
}
async function endRecording(why) {
  if (!live) return;
  live.endedAt = clock(); live.endReason = why || '手动结束'; live.recoveries = tracker.recoveries;
  const s = live; Sensors.onStep = null; live = null; liveState = 'idle'; pickMode = false; pickTarget = null; releaseAwake();
  if (s.path.length > 1) { await DB.put('sessions', s); toast(`已保存：${s.steps.length} 步，${pathLen(s).toFixed(0)} m`); libSel = new Set([s.id]); await loadSessions(); }
  else { await DB.del('sessions', s.id).catch(() => { }); toast('没有走动，没保存'); }
  tracker.p = []; tracker.last = null; tracker.recoveries = 0;
  showLive(); draw();
  if (s.path.length > 1 && !s.sim) switchTab('lib');
}
function showLive() { $('#recIdle').hidden = !!live; $('#recLive').hidden = !live; $('#pickBar').hidden = !pickMode; }
function updateLive() {
  if (!live) return;
  const e = tracker.last, last = live.anchors.at(-1), now = clock();
  const since = last ? (now - last.t) / 1000 : 0; const dist = pathLen(live);
  const spread = e && liveState === 'tracking' ? e.sd : null;
  $('#liveStats').innerHTML = [
    ['状态', liveState === 'tracking' ? '<span class="pill ok">记录中</span>' : '<span class="pill warn">等锚点</span>'],
    ['步数', live.steps.length], ['距离', dist.toFixed(1) + ' m'],
    ['用时', dur((now - live.startedAt) / 1000)], ['不确定度', spread == null ? '—' : '±' + spread.toFixed(1) + ' m'],
    ['上次校正', last ? dur(since) + ' 前' : '—']
  ].map(([a, b]) => `<div><span>${a}</span><b>${b}</b></div>`).join('');
  let hint = '';
  if (liveState === 'needsAnchor') hint = '点“手动定位”，在地图上点你站的位置和面朝的方向；有二维码的话扫码更准。';
  else if ((spread > 2 || since > 120) && floor.anchors.length) hint = '误差在变大，路过锚点扫一下。';
  else if (live.gaps.length) hint = `中途有 ${live.gaps.length} 段屏幕关闭，那段没有记录。`;
  $('#liveHint').textContent = hint;
}
setInterval(() => { if (live && !Sensors.sim) updateLive(); }, 1000);
document.addEventListener('visibilitychange', () => {
  if (!live || Sensors.sim) return;
  if (document.hidden) hiddenAt = Date.now();
  else { if (hiddenAt) { live.gaps.push({ from: hiddenAt, to: Date.now() }); toast('屏幕关闭期间没有记录。建议扫一下最近的锚点。', 4000); } hiddenAt = 0; keepAwake(); }
});
$('#btnStart').onclick = startRecording;
$('#btnEnd').onclick = () => endRecording('手动结束');
$('#btnPick').onclick = () => { pickMode = true; pickTarget = null; $('#pickOk').disabled = true; $('#pickMsg').textContent = '在地图上点你现在站的位置（点在锚点上就用锚点）。'; showLive(); };
$('#pickCancel').onclick = () => { pickMode = false; pickTarget = null; showLive(); draw(); };
$('#pickOk').onclick = () => { if (pickTarget) fixAnchor(pickTarget, true); pickMode = false; pickTarget = null; showLive(); draw(); };
$('#btnScan').onclick = () => openScanner(code => {
  const m = /^FT1\|([^|]+)\|([^|]+)$/.exec(code); if (!m) return '这不是步迹锚点码';
  const a = floor.anchors.find(q => q.id === m[2]); if (!a) return `锚点 ${m[2]} 不在当前地图上`;
  if (m[1] !== floor.id) toast('注意：这个码来自另一张地图，按锚点编号匹配了');
  return a;
}, (a, yaw) => fixAnchor(a, true, yaw));

/* ---------------- QR scanner ---------------- */
let scanStream = null, scanRAF = 0;
async function openScanner(parse, done) {
  const ov = $('#scanOv'), vid = $('#scanVideo'); ov.hidden = false; $('#scanMsg').textContent = '扫码时人面对着码站好，不用很近。';
  try { scanStream = await navigator.mediaDevices.getUserMedia({ video: { facingMode: 'environment', width: { ideal: 1280 } }, audio: false }); }
  catch { ov.hidden = true; return toast('打不开摄像头。可以用“手动定位”。', 4000); }
  vid.srcObject = scanStream; await vid.play().catch(() => { });
  const c = document.createElement('canvas'); const x = c.getContext('2d', { willReadFrequently: true });
  const det = 'BarcodeDetector' in window ? new BarcodeDetector({ formats: ['qr_code'] }) : null;
  let busy = false;
  const loop = async () => {
    scanRAF = requestAnimationFrame(loop); if (busy || vid.readyState < 2) return; busy = true;
    try {
      let txt = null;
      if (det) { const r = await det.detect(vid).catch(() => []); if (r[0]) txt = r[0].rawValue; }
      else { const w = 480, h = Math.round(480 * vid.videoHeight / vid.videoWidth) || 360; c.width = w; c.height = h; x.drawImage(vid, 0, 0, w, h); const r = jsQR(x.getImageData(0, 0, w, h).data, w, h, { inversionAttempts: 'dontInvert' }); if (r) txt = r.data; }
      if (txt) { const yaw = Sensors.yawNow(); const a = parse(txt); if (typeof a === 'string') $('#scanMsg').textContent = a; else { if (navigator.vibrate) navigator.vibrate(60); closeScanner(); done(a, yaw); } }
    } finally { busy = false; }
  };
  loop();
}
function closeScanner() { cancelAnimationFrame(scanRAF); scanStream?.getTracks().forEach(t => t.stop()); scanStream = null; $('#scanOv').hidden = true; }
$('#scanClose').onclick = closeScanner;

/* ---------------- Simulation (demo / testing without sensors) ---------------- */
let simTimer = 0;
// demo sensor error model: heading bias + gyro drift per step + jitter, step length overestimate
const simCfg = { bias: 6, drift: 0.12, noise: 5, lenErr: 1.08 };
$('#simUndo').onclick = () => { simPts.pop(); simTruth = []; draw(); };
$('#simClear').onclick = () => { simPts = []; simTruth = []; draw(); };
$('#simRun').onclick = () => runSim();
function runSim(opts = {}) {
  if (!floor || !floor.anchors.length) return toast('需要一张有锚点的地图');
  if (simPts.length < 2) return toast('先在地图上点至少两个路径点');
  const fast = opts.fast;
  // snap the first point to its nearest anchor (you always start by scanning one)
  const pts = simPts.map(p => p.slice()); const a0 = anchorNear(pts[0][0], pts[0][1], 1e9); pts.unshift([a0.x, a0.y]);
  Sensors.sim = true; simClock = Date.now(); tracker.constrain = !$('#simNoCorr').checked; tracker.recoveries = 0;
  live = newSession(true); liveState = 'needsAnchor'; live.offset = 0; showLive();
  fixAnchor(a0, false);
  // truth walk: 0.68 m steps; the "sensor" errs per simCfg (heading bias + gyro drift, longer steps)
  const truth = [{ x: a0.x, y: a0.y }]; const steps = [];
  for (let i = 1; i < pts.length; i++) {
    let [x, y] = pts[i - 1]; const [tx, ty] = pts[i]; let d = Math.hypot(tx - x, ty - y); const n = Math.max(1, Math.round(d / 0.68)); const sl = d / n; const h = n360(deg(Math.atan2(tx - x, -(ty - y))));
    for (let k = 0; k < n; k++) { x += sl * Math.sin(rad(h)); y -= sl * Math.cos(rad(h)); steps.push({ len: sl, h, x, y }); }
    const an = anchorNear(tx, ty, 0.8); if (an) steps.push({ anchor: an });
  }
  let drift = simCfg.bias, i = 0; simTruth = truth;
  const tick = () => {
    if (!live || !Sensors.sim) return;
    const s = steps[i++]; if (!s) { endRecording('演示结束'); Sensors.sim = false; return; }
    simClock += 560;
    if (s.anchor) { fixAnchor(s.anchor, false); drift = simCfg.bias * 0.3; simClock += 4000; }
    else {
      drift += simCfg.drift; simYaw = n360(s.h + drift + randn() * simCfg.noise); truth.push({ x: s.x, y: s.y });
      const len = s.len * simCfg.lenErr * (1 + randn() * 0.05); const amp = Math.pow(len / live.K, 4);
      onStep({ amp, yaw: simYaw });
    }
    if (!fast) simTimer = setTimeout(tick, 70);
  };
  if (fast) { while (live && Sensors.sim) tick(); } else tick();
}

/* ---------------- Background recordings: Sensor Logger import ----------------
   Sensor Logger (iOS/Android) keeps logging with the screen locked. We take its
   Accelerometer (linear, m/s²), Gravity (m/s²) and Gyroscope (rad/s) CSVs, detect
   steps on the vertical component, integrate the rotation rate about the gravity
   axis for heading (works whatever way the phone sits in a pocket), then run the
   same wall-constrained particle filter offline from a start point the user taps. */
const BG = { start: null, loop: true, items: [] };
function csvCols(text, want) {
  let i = text.indexOf('\n'); const head = text.slice(0, i).replace(/\r/g, '').split(',').map(h => h.trim().replace(/^"|"$/g, ''));
  const idx = want.map(w => head.indexOf(w)); if (idx.some(k => k < 0)) return null;
  const out = want.map(() => []);
  let p = i + 1; const L = text.length;
  while (p < L) {
    let e = text.indexOf('\n', p); if (e < 0) e = L; const line = text.slice(p, e); p = e + 1; if (line.length < 3) continue;
    const f = line.split(','); for (let k = 0; k < want.length; k++) out[k].push(+f[idx[k]]);
  }
  const r = {}; want.forEach((w, k) => r[w] = Float64Array.from(out[k])); return r;
}
async function readSensorLogger(file) {
  const zip = await JSZip.loadAsync(file); const byName = {};
  zip.forEach((path, f) => { if (!f.dir) byName[path.split('/').pop().toLowerCase()] = f; });
  const get = async n => byName[n] ? byName[n].async('string') : null;
  const accT = await get('accelerometer.csv'), grT = await get('gravity.csv'), gyT = await get('gyroscope.csv');
  if (!accT || !grT || !gyT) throw new Error('zip 里要有 Accelerometer、Gravity、Gyroscope 三个文件。在 Sensor Logger 里把这三个传感器打开再录。');
  const xyz = ['time', 'x', 'y', 'z'];
  const A = csvCols(accT, xyz), G = csvCols(grT, xyz), W = csvCols(gyT, xyz);
  if (!A || !G || !W) throw new Error('CSV 的列名和预期不一样（需要 time, x, y, z）。');
  for (const S of [A, G, W]) for (let i = 0; i < S.time.length; i++) S.time[i] /= 1e6; // ns → ms
  let platform = 'ios', device = '', ped = null;
  const meta = await get('metadata.csv');
  if (meta) { const [h, v] = meta.split(/\r?\n/); const H = h.split(','), V = (v || '').split(','); const pi = H.indexOf('platform'); if (pi >= 0) platform = (V[pi] || '').toLowerCase().includes('android') ? 'android' : 'ios'; const di = H.indexOf('device name'); if (di >= 0) device = V[di]; }
  let pedDist = null;
  const pedT = await get('pedometer.csv'); if (pedT) { const P = csvCols(pedT, ['time', 'steps']); if (P && P.steps.length) ped = P.steps[P.steps.length - 1] - (P.steps[0] < P.steps[P.steps.length - 1] * 0.5 ? P.steps[0] : 0); const PD = csvCols(pedT, ['time', 'distance']); if (PD && PD.distance.length && PD.distance[PD.distance.length - 1] > 0) { const d1 = PD.distance[PD.distance.length - 1]; pedDist = d1 - (PD.distance[0] < d1 * 0.5 ? PD.distance[0] : 0); } }
  return { A, G, W, platform, device, ped, pedDist, name: file.name };
}
// one pass over the samples → step events {t, amp, yaw (deg, clockwise, arbitrary zero), reorient}
function bgSteps(raw) {
  const { A, G, W } = raw; const n = A.time.length; const down = raw.platform === 'android' ? -1 : 1; // iOS gravity points down, Android's points up
  let gi = 0, wi = 0, yaw = 0, lastT = A.time[0], lp = 0, st = 0, peak = 0, peakT = 0, trough = 0, lastStepT = -1e9, avgPeak = 2;
  const ev = []; let lastStepG = null;
  for (let i = 0; i < n; i++) {
    const t = A.time[i];
    while (gi + 1 < G.time.length && G.time[gi + 1] <= t) gi++;
    while (wi + 1 < W.time.length && W.time[wi + 1] <= t) wi++;
    let gx = G.x[gi], gy = G.y[gi], gz = G.z[gi]; const gn = Math.hypot(gx, gy, gz) || 1; gx = gx / gn * down; gy = gy / gn * down; gz = gz / gn * down; // unit vector pointing down
    const dt = clamp((t - lastT) / 1000, 0, 0.2); lastT = t;
    yaw += deg(W.x[wi] * gx + W.y[wi] * gy + W.z[wi] * gz) * dt; // clockwise heading change = rotation rate about the down axis
    const v = -(A.x[i] * gx + A.y[i] * gy + A.z[i] * gz);         // upward linear acceleration
    lp += 0.3 * (v - lp);
    const thr = clamp(0.4 * avgPeak, 0.5, 2.2);
    if (st === 0) { if (lp < trough) trough = lp; if (lp > thr) { st = 1; peak = lp; peakT = t; } }
    else {
      if (lp > peak) { peak = lp; peakT = t; }
      if (lp < 0) {
        if (peakT - lastStepT > 280) {
          const g = [gx, gy, gz]; let reorient = false;
          if (lastStepG && peakT - lastStepT > 5000) { const c = g[0] * lastStepG[0] + g[1] * lastStepG[1] + g[2] * lastStepG[2]; reorient = c < Math.cos(rad(20)); }
          ev.push({ t: peakT, amp: peak - Math.min(trough, 0), yaw, reorient }); lastStepG = g;
          avgPeak = 0.8 * avgPeak + 0.2 * peak; lastStepT = peakT;
        }
        st = 0; trough = lp;
      }
    }
  }
  return ev;
}
function bgRunFilter(ev, start, end, sign, stepLen) {
  const N0 = Math.min(5, ev.length); let s = 0, c = 0; for (let i = 0; i < N0; i++) { s += Math.sin(rad(sign * ev[i].yaw)); c += Math.cos(rad(sign * ev[i].yaw)); }
  const offset = start.face - deg(Math.atan2(s, c));
  tracker.constrain = true; tracker.recoveries = 0; tracker.init(start.x, start.y, 0.4);
  for (const p of tracker.p) p.hb = randn() * 8;
  const path = [{ t: ev[0].t - 500, x: start.x, y: start.y, sd: 0.4, anchor: 'start' }], steps = []; let kills = 0;
  for (const e of ev) {
    if (e.reorient) for (const p of tracker.p) p.hb += randn() * 15;
    const h = n360(sign * e.yaw + offset); const before = tracker.p.filter(p => p.w > 0).length;
    tracker.step(stepLen, h); kills += tracker.lastKilled / Math.max(1, before);
    const q = tracker.last; steps.push({ t: e.t, len: +stepLen.toFixed(3), amp: +e.amp.toFixed(2), yaw: +(sign * e.yaw).toFixed(1), h: +h.toFixed(1) });
    path.push({ t: e.t, x: +q.x.toFixed(3), y: +q.y.toFixed(3), sd: +q.sd.toFixed(2) });
  }
  const anchors = [{ t: path[0].t, id: 'start', x: start.x, y: start.y, pathIndex: 0, estX: null, estY: null, err: null }];
  if (end) { const q = tracker.last, t = ev.at(-1).t + 500; anchors.push({ t, id: 'end', x: end.x, y: end.y, pathIndex: path.length, estX: +q.x.toFixed(3), estY: +q.y.toFixed(3), err: +Math.hypot(q.x - end.x, q.y - end.y).toFixed(2) }); path.push({ t, x: end.x, y: end.y, sd: 0.4, anchor: 'end' }); }
  return { path, steps, anchors, offset, kills: kills / ev.length, recoveries: tracker.recoveries };
}
$('#bgPick').onclick = () => $('#bgFile').click();
// several people's zips can be loaded at once; they share one start point (and, by default, the same end point)
$('#bgFile').onchange = async e => {
  const files = [...e.target.files]; e.target.value = ''; if (!files.length) return;
  for (const f of files) {
    const it = { id: uid('b'), file: f.name, name: /^[\d_-]/.test(f.name) ? '' : f.name.replace(/\.zip$/i, ''), status: '读取中…' };
    BG.items.push(it); renderBG();
    try {
      const raw = await readSensorLogger(f); const ev = bgSteps(raw);
      Object.assign(it, { ev, ped: raw.ped, pedDist: raw.pedDist, platform: raw.platform, device: raw.device, t0: raw.A.time[0], T: (raw.A.time[raw.A.time.length - 1] - raw.A.time[0]) / 1000,
        status: ev.length < 10 ? `只识别到 ${ev.length} 步，可能没在走动或少开了传感器` : '' });
    } catch (err) { it.status = '读不了：' + (err.message || err); }
    renderBG(); await new Promise(r => setTimeout(r, 0));
  }
  if (!BG.start && floor.bgStart) BG.start = { ...floor.bgStart };
  if (!BG.start) { $('#bgMsg').textContent = '在地图上点起点，再点出发后先走的方向。'; setMode('bgStart'); }
  else $('#bgMsg').textContent = '用的是上次设的起点。不对的话点“重新点起点”。';
  renderBG(); draw();
};
function bgReady() { return !!(BG.start && BG.start.face != null && BG.items.some(i => i.ev && i.ev.length >= 10)); }
function renderBG() {
  $('#bgCtl').hidden = !BG.items.length;
  $('#bgInfo').innerHTML = BG.items.map(it => {
    const st = it.status || ''; const cls = st.startsWith('已') ? 'ok' : (st.startsWith('读取') || st.startsWith('计算')) ? '' : 'bad';
    return `<div class="card"><div class="row" style="margin:0"><label>名字 <input type="text" data-bgname="${it.id}" value="${esc(it.name)}" placeholder="谁录的" maxlength="20" style="width:8em"></label><button class="b" data-bgdel="${it.id}" style="min-height:28px;padding:2px 8px">移除</button></div>
    <span class="mono" style="font-size:11.5px;color:var(--muted)">${esc(it.file)}${it.ev ? ` · ${ymd(it.t0)} ${hm(it.t0)} 起 · ${dur(it.T)} · ${it.ev.length} 步${it.ped ? '（手机计步 ' + it.ped + '）' : ''}` : ''}</span>
    ${st ? `<br><span class="pill ${cls}">${esc(st)}</span>` : ''}${it.sessionId ? ` <button class="b" data-bgflip="${it.id}" style="min-height:28px;padding:2px 8px">看着左右反了？镜像重算</button>` : ''}</div>`;
  }).join('');
  $$('#bgInfo [data-bgname]').forEach(i => i.oninput = () => { BG.items.find(q => q.id === i.dataset.bgname).name = i.value.trim(); });
  $$('#bgInfo [data-bgdel]').forEach(b => b.onclick = () => { BG.items = BG.items.filter(q => q.id !== b.dataset.bgdel); renderBG(); });
  $$('#bgInfo [data-bgflip]').forEach(b => b.onclick = async () => { const it = BG.items.find(q => q.id === b.dataset.bgflip); it.forceSign = -(it.sign || 1); await bgGenerate([it]); switchTab('lib'); });
  $('#bgRun').disabled = !bgReady();
  $('#bgRun').textContent = BG.items.length > 1 ? `生成全部 ${BG.items.length} 条轨迹` : '生成轨迹';
  $('#bgLoop').checked = BG.loop !== false;
}
$('#bgLoop').onchange = e => { BG.loop = e.target.checked; };
$('#bgSetStart').onclick = () => { BG.start = null; $('#bgRun').disabled = true; $('#bgMsg').textContent = '在地图上点起点，再点出发后先走的方向。'; setMode('bgStart'); draw(); };
function bgTap(x, y) {
  if (!BG.start || BG.start.face != null) { if (isWallAt(x, y)) return toast('这里是墙'); BG.start = { x, y, face: null }; $('#bgMsg').textContent = '再点一下出发后先走的方向。'; }
  else { BG.start.face = n360(deg(Math.atan2(x - BG.start.x, -(y - BG.start.y)))); floor.bgStart = { ...BG.start }; saveFloor(); $('#bgMsg').textContent = '起点已设，会记住，下次不用再点。'; setMode('view'); renderBG(); }
  draw();
}
async function bgGenerate(items) {
  $('#bgRun').disabled = true; const done = [];
  for (const it of items) {
    if (!it.ev || it.ev.length < 10) continue;
    it.status = '计算中…'; renderBG(); await new Promise(r => setTimeout(r, 20));
    // step length: the phone's own pedometer distance when it logged one, else a typical adult step
    let len = 0.68; if (it.pedDist && it.ped) { const L = it.pedDist / it.ped; if (L > 0.4 && L < 1) len = L; }
    if (it.ped) { const r = it.ped / it.ev.length; if (r > 1.6 && r < 2.4) len *= r; } // pocket: one detected peak per stride
    const end = BG.loop !== false ? { x: BG.start.x, y: BG.start.y } : null;
    let best;
    if (it.forceSign) { best = bgRunFilter(it.ev, BG.start, end, it.forceSign, len); it.sign = it.forceSign; it.forceSign = 0; }
    else { const a = bgRunFilter(it.ev, BG.start, end, 1, len), b = bgRunFilter(it.ev, BG.start, end, -1, len); const flip = b.kills + 0.02 < a.kills; best = flip ? b : a; it.sign = flip ? -1 : 1; }
    const t0 = best.path[0].t; const who = it.name || '未命名';
    const s = { id: it.sessionId || uid('s'), format: 'footfall-trace/v1', source: 'sensorlogger', sourceFile: it.file, floorId: floor.id, floorName: floor.name, participant: who, participantId: 'name:' + who, K: null, calibrated: !!it.pedDist,
      sim: false, date: ymd(t0), startedAt: t0, endedAt: best.path[best.path.length - 1].t, offset: +best.offset.toFixed(1), steps: best.steps, path: best.path, anchors: best.anchors, gaps: [], recoveries: best.recoveries, device: it.device || it.platform, endReason: '后台记录导入' };
    it.sessionId = s.id; await DB.put('sessions', s); done.push(s.id);
    it.status = `已生成 ${pathLen(s).toFixed(0)} m` + (best.anchors[1] ? `，回到起点时偏差 ${best.anchors[1].err} m（已拉回）` : '');
    renderBG();
  }
  tracker.p = []; tracker.last = null;
  await loadSessions();
  if (done.length) { libSel = new Set(done); renderLib(); $('#bgMsg').textContent = `生成了 ${done.length} 条。去“记录库”看，可以叠在一起看或者看热力图，再导出 CSV。`; }
  renderBG();
}
$('#bgRun').onclick = () => { if (bgReady()) bgGenerate(BG.items); };

/* ---------------- Calibration ---------------- */
let calRun = null, testRun = null;
function refreshCalPairs() {
  if (!floor) return; const a = floor.anchors; let o = '<option value="">或选两个锚点…</option>';
  for (let i = 0; i < a.length; i++) for (let j = i + 1; j < a.length; j++) { const d = Math.hypot(a[i].x - a[j].x, a[i].y - a[j].y); if (d > 3 && !segBlocked(a[i].x, a[i].y, a[j].x, a[j].y)) o += `<option value="${d.toFixed(2)}">${a[i].id} → ${a[j].id}（直线 ${d.toFixed(1)} m）</option>`; }
  $('#calPair').innerHTML = o;
}
$('#calPair').onchange = e => { if (e.target.value) $('#calDist').value = e.target.value; };
$('#calGo').onclick = async () => {
  try { await Sensors.start(); } catch (err) { return toast(err.message, 6000); }
  keepAwake(); calRun = { n: 0, sum: 0 };
  Sensors.onStep = ({ amp }) => { if (!calRun) return; calRun.n++; calRun.sum += Math.pow(Math.max(amp, 0.05), 0.25); $('#calLive').textContent = calRun.n + ' 步'; };
  $('#calGo').disabled = true; $('#calStop').disabled = false; $('#calLive').textContent = '0 步 · 走吧';
};
$('#calStop').onclick = () => {
  const r = calRun; calRun = null; Sensors.onStep = null; releaseAwake(); $('#calGo').disabled = false; $('#calStop').disabled = true;
  const D = +$('#calDist').value; if (!r || r.n < 6) { $('#calResult').innerHTML = '<p class="hint">步数太少，没有算。至少走 6 步以上。</p>'; return; }
  const K = D / r.sum; const p = prof();
  if (K < 0.25 || K > 0.8) { $('#calResult').innerHTML = `<div class="card"><span class="pill bad">异常</span> 算出 K = ${K.toFixed(3)}，${r.n} 步走 ${D} m，看起来步数没数准。确认手机拿稳、正常步速，再走一次。</div>`; return; }
  p.K = p.calibrated ? (p.K * (p.calN || 1) + K) / ((p.calN || 1) + 1) : K; p.calN = (p.calibrated ? (p.calN || 1) + 1 : 1); p.calibrated = true; saveProfiles();
  $('#calResult').innerHTML = `<div class="card"><span class="pill ok">已保存</span> ${r.n} 步 / ${D} m = 平均 ${(D / r.n).toFixed(2)} m/步。本次 K = ${K.toFixed(3)}，累计平均 ${p.K.toFixed(3)}。</div>`;
};
$('#testGo').onclick = async () => {
  if (testRun) { clearInterval(testRun); testRun = null; Sensors.onStep = null; $('#testGo').textContent = '开始测试'; return; }
  try { await Sensors.start(); } catch (err) { return toast(err.message, 6000); }
  const c0 = Sensors.count; Sensors.onStep = () => { };
  testRun = setInterval(() => { const y = Sensors.yawNow(); $('#testLive').textContent = `${Sensors.count - c0} 步 · 方向 ${y == null ? '—' : y.toFixed(0) + '°'}${Sensors.compass != null ? ' · 指南针 ' + Sensors.compass.toFixed(0) + '°' : ''}`; }, 200);
  $('#testGo').textContent = '停止测试';
};

/* ---------------- Path correction + analysis ---------------- */
function correctedPath(s) {
  const P = s.path.map(p => ({ t: p.t, x: p.x, y: p.y, anchor: p.anchor }));
  const A = s.anchors; let prev = null;
  for (const a of A) {
    if (prev && a.estX != null) {
      const i0 = prev.pathIndex, i1 = a.pathIndex, t0 = prev.t, t1 = a.t; const ex = a.x - a.estX, ey = a.y - a.estY;
      for (let j = i0 + 1; j < i1; j++) { const w = t1 > t0 ? (P[j].t - t0) / (t1 - t0) : 1; P[j].x += ex * w; P[j].y += ey * w; }
    }
    prev = a;
  }
  return P;
}
function pathLen(s) { let d = 0; for (let i = 1; i < s.path.length; i++) if (!s.path[i].anchor) d += Math.hypot(s.path[i].x - s.path[i - 1].x, s.path[i].y - s.path[i - 1].y); return d; }
function dwells(P, minS = 4) { const out = []; for (let i = 1; i < P.length; i++) { const dt = (P[i].t - P[i - 1].t) / 1000; if (dt >= minS) out.push({ x: P[i - 1].x, y: P[i - 1].y, s: dt }); } return out; }

/* ---------------- Library ---------------- */
let sessions = [], libSel = new Set(LS.get('libSel', [])), playFrac = 1;
async function loadSessions() { sessions = (await DB.all('sessions')).sort((a, b) => b.startedAt - a.startedAt); renderLib(); }
function sessColor(s) { const i = sessions.filter(q => q.floorId === s.floorId).findIndex(q => q.id === s.id); return PALETTE[(i < 0 ? 0 : i) % PALETTE.length]; }
function renderLib() {
  if (!floor) return;
  const mine = sessions.filter(s => s.floorId === floor.id && s.id !== live?.id);
  const days = {}; mine.forEach(s => (days[s.date] ||= []).push(s));
  let h = '';
  if (!mine.length) h = '<p class="hint">这张地图还没有记录。去“记录”开始一次，或者用演示模式试一下。导入组员发来的 JSON 也会出现在这里。</p>';
  for (const d of Object.keys(days).sort().reverse()) {
    h += `<div class="day">${d}<button class="b" data-day="${d}" style="min-height:26px;padding:2px 8px;font-size:12px">选这天</button></div>`;
    for (const s of days[d]) {
      const len = pathLen(s), mins = ((s.endedAt || s.path.at(-1)?.t || s.startedAt) - s.startedAt) / 60000;
      h += `<label class="sess"><input type="checkbox" data-id="${s.id}" ${libSel.has(s.id) ? 'checked' : ''}><span class="sw" style="background:${sessColor(s)}"></span>
        <span><b>${esc(s.participant)}</b> <button class="b" data-ren="${s.id}" style="min-height:22px;padding:0 6px;font-size:11px">改名</button>${s.sim ? ' <span class="pill">演示</span>' : ''}${s.source === 'sensorlogger' ? ' <span class="pill">后台</span>' : ''}${s.calibrated ? '' : ' <span class="pill warn">未校准</span>'}<br>
        <span class="meta">${hm(s.startedAt)}–${hm(s.endedAt || s.startedAt)} · ${mins.toFixed(0)} 分 · ${s.steps.length} 步 · ${len.toFixed(0)} m · 校正 ${Math.max(0, s.anchors.length - 1)} 次${s.anchors.length > 1 ? ' · 平均偏差 ' + avgErr(s) + ' m' : ''}</span></span></label>`;
    }
  }
  $('#libList').innerHTML = h;
  $$('#libList input[data-id]').forEach(c => c.onchange = () => { c.checked ? libSel.add(c.dataset.id) : libSel.delete(c.dataset.id); libChanged(); });
  $$('#libList button[data-ren]').forEach(b => b.onclick = e => {
    e.preventDefault(); const s = sessions.find(q => q.id === b.dataset.ren); const name = b.previousElementSibling;
    const inp = document.createElement('input'); inp.type = 'text'; inp.value = s.participant; inp.maxLength = 20; inp.style.width = '8em';
    const ok = document.createElement('button'); ok.className = 'b'; ok.textContent = '保存';
    ok.onclick = async ev => { ev.preventDefault(); s.participant = inp.value.trim() || s.participant; s.participantId = 'name:' + s.participant; await DB.put('sessions', s); renderLib(); };
    name.hidden = true; b.replaceWith(inp, ok); inp.focus();
  });
  $$('#libList button[data-day]').forEach(b => b.onclick = e => { e.preventDefault(); mine.filter(s => s.date === b.dataset.day).forEach(s => libSel.add(s.id)); renderLib(); libChanged(); });
  libChanged(false);
}
function avgErr(s) { const e = s.anchors.filter(a => a.err != null).map(a => a.err); return e.length ? (e.reduce((a, b) => a + b, 0) / e.length).toFixed(1) : '—'; }
function selSessions() { return sessions.filter(s => libSel.has(s.id) && floor && s.floorId === floor.id); }
function libChanged(redraw = true) {
  LS.set('libSel', [...libSel]); const sel = selSessions(); $('#playRow').hidden = sel.length !== 1;
  if (sel.length === 1) { const s = sel[0]; const T = ((s.endedAt || s.path.at(-1).t) - s.startedAt) / 1000; $('#playT').textContent = dur(T * playFrac) + ' / ' + dur(T); }
  if (redraw) draw();
}
$('#play').oninput = e => { playFrac = e.target.value / 1000; libChanged(); };
$('#libAll').onclick = () => { const d = sessions.find(s => s.floorId === floor.id)?.date; sessions.filter(s => s.floorId === floor.id && s.date === d).forEach(s => libSel.add(s.id)); renderLib(); libChanged(); };
$('#libNone').onclick = () => { libSel.clear(); renderLib(); libChanged(); };
$('#libHeat').onchange = draw; $('#libRaw').onchange = draw;
function drawLibrary() {
  const sel = selSessions(); if (!sel.length) return;
  if ($('#libHeat').checked) {
    const C = 0.5, cw = Math.ceil(floorWH().W / C), ch = Math.ceil(floorWH().H / C); const acc = new Float32Array(cw * ch); let mx = 0;
    for (const s of sel) { const P = correctedPath(s); for (let i = 1; i < P.length; i++) { const dt = Math.min(120, (P[i].t - P[i - 1].t) / 1000); const cx = Math.floor(P[i - 1].x / C), cy = Math.floor(P[i - 1].y / C); if (cx < 0 || cy < 0 || cx >= cw || cy >= ch) continue; const k = cy * cw + cx; acc[k] += dt; if (acc[k] > mx) mx = acc[k]; } }
    ctx.fillStyle = css('--signal');
    for (let k = 0; k < acc.length; k++) if (acc[k]) { ctx.globalAlpha = 0.12 + 0.75 * Math.sqrt(acc[k] / mx); ctx.fillRect((k % cw) * C, Math.floor(k / cw) * C, C, C); }
    ctx.globalAlpha = 1; return;
  }
  for (const s of sel) {
    const col = sessColor(s); let P = correctedPath(s);
    if (sel.length === 1 && playFrac < 1) { const tEnd = s.startedAt + ((s.endedAt || P.at(-1).t) - s.startedAt) * playFrac; P = P.filter(p => p.t <= tEnd); }
    if ($('#libRaw').checked) polyline(sel.length === 1 && playFrac < 1 ? s.path.slice(0, P.length) : s.path, col, 1.2, [px(4), px(4)]);
    polyline(P, col, 2.6);
    ctx.fillStyle = col; ctx.globalAlpha = 0.25; for (const d of dwells(P)) { ctx.beginPath(); ctx.arc(d.x, d.y, clamp(Math.sqrt(d.s) * 0.18, 0.25, 2.5), 0, 7); ctx.fill(); } ctx.globalAlpha = 1;
    const e = P.at(-1); if (e) { ctx.beginPath(); ctx.arc(e.x, e.y, px(4.5), 0, 7); ctx.fill(); }
  }
}
function exportList() { const s = selSessions(); return s.length ? s : sessions.filter(q => q.floorId === floor.id); }
function floorMeta() { return { id: floor.id, name: floor.name, widthM: +floorWH().W.toFixed(2), heightM: +floorWH().H.toFixed(2), anchors: floor.anchors }; }
$('#expJson').onclick = () => {
  const L = exportList(); if (!L.length) return toast('没有可导出的记录');
  const out = { format: 'footfall-trace/v1', exportedAt: new Date().toISOString(), units: 'metres; x right, y down, origin top-left of plan; heading deg clockwise from plan-up', floor: floorMeta(), sessions: L.map(s => ({ ...s, corrected: correctedPath(s).map(p => ({ t: p.t, x: +p.x.toFixed(3), y: +p.y.toFixed(3) })) })) };
  saveFile(`footfall_${floor.id}_${dateRange(L)}.json`, JSON.stringify(out), 'application/json');
};
$('#expCsv').onclick = () => {
  const L = exportList(); if (!L.length) return toast('没有可导出的记录');
  const rows = ['session_id,participant,date,time_iso,t_s,x_m,y_m,x_raw_m,y_raw_m,uncertainty_m,anchor'];
  for (const s of L) { const C = correctedPath(s); s.path.forEach((p, i) => rows.push([s.id, JSON.stringify(s.participant), s.date, new Date(p.t).toISOString(), ((p.t - s.startedAt) / 1000).toFixed(2), C[i].x.toFixed(3), C[i].y.toFixed(3), p.x.toFixed(3), p.y.toFixed(3), p.sd ?? '', p.anchor || ''].join(','))); }
  saveFile(`footfall_${floor.id}_${dateRange(L)}.csv`, '﻿' + rows.join('\n'), 'text/csv');
};
function dateRange(L) { const d = L.map(s => s.date).sort(); return d[0] === d.at(-1) ? d[0] : d[0] + '_' + d.at(-1); }
async function saveFile(name, text, type) {
  const blob = new Blob([text], { type });
  try { const f = new File([blob], name, { type }); if (matchMedia('(pointer:coarse)').matches && navigator.canShare?.({ files: [f] })) { await navigator.share({ files: [f], title: name }); return; } }
  catch (e) { if (e.name === 'AbortError') return; }
  const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name; document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
}
$('#impBtn').onclick = () => $('#impFile').click();
$('#impFile').onchange = async e => { for (const f of e.target.files) await importFile(f); e.target.value = ''; };
async function importFile(f) {
  let j; try { j = JSON.parse(await f.text()); } catch { return toast(f.name + ' 不是有效的 JSON'); }
  if (j.format === 'footfall-floor/v1') return importFloor(j);
  if (j.format !== 'footfall-trace/v1' || !Array.isArray(j.sessions)) return toast(f.name + ' 不是步迹导出的文件');
  for (const s of j.sessions) { delete s.corrected; await DB.put('sessions', s); libSel.add(s.id); }
  await loadSessions();
  const other = j.sessions.filter(s => s.floorId !== floor.id).length;
  toast(`导入 ${j.sessions.length} 条记录` + (other ? `，其中 ${other} 条属于另一张地图（${j.floor?.name || ''}），切换地图后可见` : ''), 4500);
}
$('#libDel').onclick = () => { const L = selSessions(); if (!L.length) return toast('先勾选要删除的记录'); $('#delMsg').textContent = `删除选中的 ${L.length} 条记录？删除后不能恢复，建议先导出。`; $('#delConfirm').hidden = false; };
$('#delNo').onclick = () => $('#delConfirm').hidden = true;
$('#delYes').onclick = async () => { for (const s of selSessions()) { await DB.del('sessions', s.id); libSel.delete(s.id); } $('#delConfirm').hidden = true; await loadSessions(); draw(); };

/* ---------------- Setup ---------------- */
let mode = 'view', scalePts = [], selAnchor = null;
function setMode(m) {
  mode = m; scalePts = []; $('#scaleRow').hidden = true; brushCursor = null;
  const map = { scale: '#mScale', wall: '#mWall', erase: '#mErase', anchor: '#mAnchor', view: '#mPan' };
  Object.entries(map).forEach(([k, s]) => $(s).classList.toggle('on', k === m));
  $('#modeChip').textContent = { scale: '比例尺：点两个已知距离的点', wall: '画墙：拖动涂抹 · 双指缩放', erase: '擦除：拖动涂掉误判的墙 · 双指缩放', anchor: '锚点：点空白处新建，点已有的选中', bgStart: '后台记录：点起点，再点出发方向' }[m] || '';
  draw();
}
$('#mScale').onclick = () => setMode(mode === 'scale' ? 'view' : 'scale');
$('#mWall').onclick = () => setMode(mode === 'wall' ? 'view' : 'wall');
$('#mErase').onclick = () => setMode(mode === 'erase' ? 'view' : 'erase');
$('#mPan').onclick = () => setMode('view');
$('#mAnchor').onclick = () => setMode(mode === 'anchor' ? 'view' : 'anchor');
$('#scaleApply').onclick = async () => {
  const D = +$('#scaleDist').value; if (!(D > 0) || scalePts.length !== 2) return toast('输入两点间的实际距离');
  const dm = Math.hypot(scalePts[0][0] - scalePts[1][0], scalePts[0][1] - scalePts[1][1]); // metres under current scale
  const f = dm / D; const old = floor.pxPerM; floor.pxPerM = old * f;
  floor.anchors.forEach(a => { a.x = +(a.x / f).toFixed(2); a.y = +(a.y / f).toFixed(2); });
  floor.overrides = null; rebuildImageGrid(); await saveFloor(); setMode('view'); fitView(); refreshSetup(); refreshCalPairs(); toast('比例尺已更新');
};
$('#useImg').onchange = e => { floor.useImageWalls = e.target.checked; rebuildWalls(); draw(); saveFloor(); };
$('#thr').oninput = e => { floor.threshold = +e.target.value; rebuildWalls(); draw(); };
$('#thr').onchange = () => saveFloor();
$('#ovClear').onclick = () => { floor.overrides.fill(0); rebuildWalls(); draw(); saveFloor(); toast('已清除手动修改'); };
$('#floorName').onchange = e => { floor.name = e.target.value.trim() || floor.name; $('#hdrFloor').textContent = floor.name; saveFloor(); refreshFloorSel(); };
function refreshSetup() {
  if (!floor) return; $('#floorName').value = floor.name; $('#useImg').checked = floor.useImageWalls; $('#thr').value = floor.threshold;
  const { W, H } = floorWH(); $('#scaleInfo').textContent = `1 m = ${floor.pxPerM.toFixed(1)} px · 全图 ${W.toFixed(1)} × ${H.toFixed(1)} m`;
  refreshAnchorEd();
}
function refreshAnchorEd() {
  const a = floor.anchors.find(q => q.id === selAnchor); $('#anchorEd').hidden = !a; if (!a) return;
  $('#aId').textContent = a.id; $('#aLabel').value = a.label || ''; $('#aFace').textContent = a.face == null ? '未设' : Math.round(a.face) + '°'; $('#aExit').checked = a.type === 'exit';
}
const curA = () => floor.anchors.find(q => q.id === selAnchor);
$('#aLabel').onchange = e => { curA().label = e.target.value.trim(); saveFloor(); draw(); };
$('#aRotL').onclick = () => { const a = curA(); a.face = n360((a.face ?? 0) - 15); refreshAnchorEd(); saveFloor(); draw(); };
$('#aRotR').onclick = () => { const a = curA(); a.face = n360((a.face ?? 0) + 15); refreshAnchorEd(); saveFloor(); draw(); };
$('#aAuto').onclick = () => { const a = curA(); const f = nearestWallDir(a.x, a.y); if (f == null) return toast('2.5 m 内没有墙'); a.face = f; refreshAnchorEd(); saveFloor(); draw(); };
$('#aExit').onchange = e => { curA().type = e.target.checked ? 'exit' : 'normal'; saveFloor(); draw(); };
$('#aDel').onclick = () => { floor.anchors = floor.anchors.filter(q => q.id !== selAnchor); selAnchor = null; refreshAnchorEd(); saveFloor(); refreshCalPairs(); draw(); };
$('#printQR').onclick = () => {
  if (!floor.anchors.length) return toast('还没有锚点');
  $('#sheet').innerHTML = `<p class="hint">地图：${esc(floor.name)}。打印后按地图上的位置贴，胸口高度，码的正面朝向地图上箭头的反方向（人站在锚点位置能正对着它）。</p><div class="qrgrid">` + floor.anchors.map(a => {
    const q = qrcode(0, 'M'); q.addData(`FT1|${floor.id}|${a.id}`); q.make();
    return `<div class="qr"><div class="id">${a.id}</div><div class="lb">${esc(a.label || '')}${a.type === 'exit' ? ' · 出口' : ''}</div>${q.createSvgTag({ cellSize: 6, margin: 12, scalable: true })}<div class="ins">步迹 · ${esc(floor.name)}<br>面对此码站好再扫${a.type === 'exit' ? '，扫完自动结束' : ''}</div></div>`;
  }).join('') + '</div>';
  $('#sheetOv').hidden = false;
};
$('#sheetClose').onclick = () => $('#sheetOv').hidden = true;
$('#sheetPrint').onclick = () => window.print();
async function refreshFloorSel() {
  const all = await DB.all('floors'); $('#floorSel').innerHTML = all.map(f => `<option value="${f.id}"${floor && f.id === floor.id ? ' selected' : ''}>${esc(f.name)}</option>`).join('');
}
$('#floorSel').onchange = async e => { const f = await DB.get('floors', e.target.value); if (f) setFloor(f); };
$('#floorSample').onclick = async () => { let f = await DB.get('floors', 'sample-studio'); if (!f) { f = await makeSampleFloor(); await DB.put('floors', f); } setFloor(f); };
$('#floorUpload').onclick = () => $('#floorFile').click();
$('#floorFile').onchange = async e => {
  const file = e.target.files[0]; e.target.value = ''; if (!file) return;
  const url = await new Promise(r => { const fr = new FileReader(); fr.onload = () => r(fr.result); fr.readAsDataURL(file); });
  let im; try { im = await loadImage(url); } catch { return toast('读不了这张图片'); }
  // keep the plan at ≤ 2400 px on the long side
  const sc = Math.min(1, 2400 / Math.max(im.width, im.height)); const c = document.createElement('canvas'); c.width = Math.round(im.width * sc); c.height = Math.round(im.height * sc); c.getContext('2d').drawImage(im, 0, 0, c.width, c.height);
  const f = { id: 'f' + Date.now().toString(36), name: file.name.replace(/\.[^.]+$/, ''), image: c.toDataURL('image/jpeg', 0.9), imgW: c.width, imgH: c.height, pxPerM: c.width / 40, threshold: 110, useImageWalls: true, overrides: null, anchors: [], createdAt: Date.now() };
  await DB.put('floors', f); await setFloor(f); setMode('scale'); toast('先定比例尺：在图上点两个知道实际距离的点', 5000);
};
$('#floorExp').onclick = () => {
  const out = { format: 'footfall-floor/v1', id: floor.id, name: floor.name, image: floor.image, imgW: floor.imgW, imgH: floor.imgH, pxPerM: floor.pxPerM, threshold: floor.threshold, useImageWalls: floor.useImageWalls, anchors: floor.anchors, gw, gh, overrides: rle(floor.overrides) };
  saveFile(`footfall-floor_${floor.id}.json`, JSON.stringify(out), 'application/json');
};
$('#floorImp').onclick = () => $('#floorImpFile').click();
$('#floorImpFile').onchange = async e => { const f = e.target.files[0]; e.target.value = ''; if (f) importFile(f); };
async function importFloor(j) {
  const f = { id: j.id, name: j.name, image: j.image, imgW: j.imgW, imgH: j.imgH, pxPerM: j.pxPerM, threshold: j.threshold ?? 110, useImageWalls: j.useImageWalls !== false, anchors: j.anchors || [], gw: j.gw, gh: j.gh, overrides: j.overrides ? unrle(j.overrides, j.gw * j.gh) : null, createdAt: Date.now() };
  await DB.put('floors', f); await setFloor(f); toast('已导入地图：' + f.name);
}
$('#floorDel').onclick = async () => {
  const all = await DB.all('floors'); if (all.length < 2) return toast('至少要留一张地图');
  if ($('#floorDel').dataset.armed !== '1') { $('#floorDel').dataset.armed = '1'; $('#floorDel').textContent = '再点一次确认删除'; setTimeout(() => { $('#floorDel').dataset.armed = ''; $('#floorDel').textContent = '删除此地图'; }, 3000); return; }
  await DB.del('floors', floor.id); const next = (await DB.all('floors'))[0]; setFloor(next);
};

/* ---------------- Tabs ---------------- */
let tab = 'rec';
function switchTab(t) {
  tab = t; $$('.tabs button').forEach(b => b.setAttribute('aria-selected', b.dataset.tab === t)); $$('.pane').forEach(p => p.hidden = p.id !== 'pane-' + t);
  if (t !== 'setup') setMode('view'); else $('#modeChip').textContent = '';
  if (t === 'rec' && !live) $('#modeChip').textContent = simPts.length ? '' : '';
  draw();
}
$$('.tabs button').forEach(b => b.onclick = () => switchTab(b.dataset.tab));

/* ---------------- Boot ---------------- */
function sensorStatus() {
  const bits = [];
  bits.push(window.isSecureContext ? '<span class="pill ok">HTTPS</span>' : '<span class="pill bad">非 HTTPS，传感器不可用</span>');
  if (typeof DeviceMotionEvent === 'undefined' || !matchMedia('(pointer:coarse)').matches) bits.push('<span class="pill warn">看起来不是手机，可用演示模式</span>');
  $('#sensorRow').innerHTML = bits.join(' ');
}
(async function boot() {
  await DB.open();
  refreshProfiles(); sensorStatus();
  new ResizeObserver(resize).observe(cv);
  // ?floor=<url of a floor pack json> lets you share a ready-made floor by link
  const q = new URLSearchParams(location.search).get('floor');
  if (q) { try { const j = await (await fetch(q)).json(); if (j.format === 'footfall-floor/v1') { const have = await DB.get('floors', j.id); if (!have) await importFloor(j); else await setFloor(have); } } catch { toast('链接里的地图包加载失败'); } }
  if (!floor) {
    let f = await DB.get('floors', LS.get('floorId', '')); if (!f) f = (await DB.all('floors'))[0];
    if (!f) { f = await makeSampleFloor(); await DB.put('floors', f); }
    await setFloor(f);
  }
  await loadSessions();
  if (!sessions.length && floor.id === 'sample-studio') { // first run: a short demo walk so the page opens with something on it
    simPts = [[6.6, 9.5], [6.6, 6.8], [7.2, 4.6], [13, 4.4], [13, 7.2], [17.6, 9.3], [16, 12], [16, 15.5], [17, 18.8]];
    runSim({ fast: true }); simPts = []; switchTab('lib'); toast('这是一条演示轨迹。去“记录”开始真实记录。', 4000);
  }
  if ('serviceWorker' in navigator && location.protocol === 'https:') navigator.serviceWorker.register('sw.js').catch(() => { });
})();

window.__FT = { runSim, segBlocked, simCfg, get simTruth() { return simTruth; }, get sessions() { return sessions; }, get floor() { return floor; }, setSimPts: p => { simPts = p; }, correctedPath, tracker, switchTab };
