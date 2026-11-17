import { initAudio, sfx } from './audio.js';

// ───────────────────────── constantes ─────────────────────────
const W = 7000;                 // lado del mundo
const G = 256, GS = W / G;      // grilla de tierra / temperatura
const MOBILE = matchMedia('(pointer: coarse)').matches;
const SEED = 7;
const MAX_CELLS = 16;
const SPLIT_MIN = 30, EJECT_MIN = 30, EJECT_COST = 14, EJECT_GIVE = 11;
const PEAK_POP = 150;           // masa desde la que una montaña te despedaza
const EAT = 1.25;               // hay que pesar 25 % más para tragar
const START_M = 10;

const CATS = [
  ['Perturbación', 0], ['Depresión tropical', 50], ['Tormenta tropical', 63],
  ['Huracán Cat 1', 119], ['Huracán Cat 2', 154], ['Huracán Cat 3', 178], ['Huracán Cat 4', 209], ['Huracán Cat 5', 252],
];
const windOf = (m) => 20 + 7.5 * Math.sqrt(m);
const catOf = (m) => { const w = windOf(m); let i = 0; while (i + 1 < CATS.length && w >= CATS[i + 1][1]) i++; return i; };
const radius = (m) => 6 * Math.sqrt(m);
const speedOf = (m) => 330 * Math.pow(m, -0.3);
const mergeTime = (m) => 10 + m * 0.012;

const KINDS = {
  vapor:      { m: 1,   need: 0,   where: 'sea',   n: 1300, r: 8 },
  boat:       { m: 3,   need: 13,  where: 'sea',   n: 160, r: 9, move: 24 },
  palm:       { m: 4,   need: 15,  where: 'land',  n: 300, r: 10 },
  house:      { m: 10,  need: 26,  where: 'town',  n: 200, r: 14 },
  lighthouse: { m: 18,  need: 36,  where: 'coast', n: 32,  r: 13 },
  ship:       { m: 30,  need: 50,  where: 'sea',   n: 50,  r: 26, move: 15 },
  hotel:      { m: 55,  need: 70,  where: 'town',  n: 55,  r: 30 },
  platform:   { m: 110, need: 105, where: 'sea',   n: 16,  r: 40 },
  cloud:      { m: EJECT_GIVE, need: 0, r: 15 },
};

const NAMES = ['Andrés', 'Beatriz', 'Carlos', 'Dolores', 'Enrique', 'Fernanda', 'Guillermo', 'Hilda', 'Ignacio', 'Jimena', 'Kiko', 'Linda',
  'Marty', 'Nora', 'Olaf', 'Patricia', 'Ramón', 'Sandra', 'Teodoro', 'Vivian', 'Waldo', 'Ximena', 'Yolanda', 'Zacarías', 'Otto', 'Mitch',
  'Iris', 'Juana', 'César', 'Flora', 'Gilberto', 'Matilde'];
const COLORS = ['#ff6b6b', '#ffb347', '#ffe066', '#9be15d', '#48e5c2', '#4fc3f7', '#7c8cff', '#c77dff', '#ff7ac6', '#ff9f80', '#a3f7bf',
  '#f4a3ff', '#ffd6a5', '#80ffdb', '#ff5d8f', '#c0ff5a', '#ffa600', '#6ec1ff', '#e0aaff', '#f7b267'];
const PLAYER_COLOR = '#5fd4ff';

// ───────────────────────── ruido ─────────────────────────
function hash(x, y, s) {
  let h = (x * 374761393 + y * 668265263 + s * 982451653) | 0;
  h = Math.imul(h ^ (h >>> 13), 1274126177);
  return ((h ^ (h >>> 16)) >>> 0) / 4294967295;
}
function vnoise(x, y, s) {
  const xi = Math.floor(x), yi = Math.floor(y), xf = x - xi, yf = y - yi;
  const u = xf * xf * (3 - 2 * xf), v = yf * yf * (3 - 2 * yf);
  const a = hash(xi, yi, s), b = hash(xi + 1, yi, s), c = hash(xi, yi + 1, s), d = hash(xi + 1, yi + 1, s);
  return a + (b - a) * u + (c - a) * v + (a - b - c + d) * u * v;
}
function fbm(x, y, s, o) {
  let t = 0, a = 0.5, f = 1, n = 0;
  for (let i = 0; i < o; i++) { t += vnoise(x * f, y * f, s + i * 17) * a; n += a; a *= 0.5; f *= 2; }
  return t / n;
}
function mulberry(a) { return () => { a |= 0; a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
const smooth = (a, b, x) => { const t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
const mix = (a, b, t) => [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t];

// ───────────────────────── mundo ─────────────────────────
const heightG = new Float32Array(G * G), tempG = new Float32Array(G * G);
let TH = 0.6, TW = 0.6;
const islets = [], peaks = [], towns = [];

function baseH(x, y) {
  const nx = x / W, ny = y / W;
  let h = fbm(nx * 7, ny * 7, SEED, 5);
  const e = Math.min(nx, ny, 1 - nx, 1 - ny);
  return h - Math.max(0, 0.12 - e) * 3;
}
function hAt(x, y) {
  let h = baseH(x, y);
  for (const s of islets) {
    const dx = x - s.x, dy = y - s.y;
    if (Math.abs(dx) > s.R || Math.abs(dy) > s.R) continue;
    const d2 = dx * dx + dy * dy;
    if (d2 < s.R * s.R) { const k = 1 - d2 / (s.R * s.R); h += s.add * k * k; }
  }
  return h;
}
const tAt = (x, y) => fbm(x / W * 2.6, y / W * 2.6, SEED + 40, 3);
const gi = (x, y) => clamp(Math.floor(y / GS), 0, G - 1) * G + clamp(Math.floor(x / GS), 0, G - 1);
const isLand = (x, y) => (x < 0 || y < 0 || x >= W || y >= W) ? false : heightG[gi(x, y)] > TH;
const warmAt = (x, y) => smooth(TW, TW + 0.05, tempG[gi(x, y)]);
function coastal(x, y) {
  if (!isLand(x, y)) return false;
  for (let a = 0; a < 8; a++) if (!isLand(x + Math.cos(a * 0.785) * 60, y + Math.sin(a * 0.785) * 60)) return true;
  return false;
}

function genWorld() {
  const rnd = mulberry(SEED);
  const vals = new Float32Array(G * G);
  for (let j = 0; j < G; j++) for (let i = 0; i < G; i++) vals[j * G + i] = baseH((i + 0.5) * GS, (j + 0.5) * GS);
  TH = Float32Array.from(vals).sort()[Math.floor(G * G * 0.8)];
  let tries = 0;
  while (islets.length < 24 && tries++ < 6000) {
    const x = 350 + rnd() * (W - 700), y = 350 + rnd() * (W - 700);
    const b = baseH(x, y);
    if (b > TH - 0.07) continue;
    if (islets.some((s) => Math.hypot(s.x - x, s.y - y) < 750)) continue;
    islets.push({ x, y, R: 75 + rnd() * 45, add: TH + 0.17 - b });
  }
  const temps = new Float32Array(G * G);
  for (let j = 0; j < G; j++) for (let i = 0; i < G; i++) {
    const x = (i + 0.5) * GS, y = (j + 0.5) * GS;
    heightG[j * G + i] = hAt(x, y);
    temps[j * G + i] = tempG[j * G + i] = tAt(x, y);
  }
  TW = temps.sort()[Math.floor(G * G * 0.62)];
  for (const s of islets) peaks.push({ x: s.x, y: s.y, r: 44 });
  const cand = [];
  for (let j = 2; j < G - 2; j++) for (let i = 2; i < G - 2; i++) {
    const h = heightG[j * G + i];
    if (h < TH + 0.1) continue;
    let top = true;
    for (let dj = -2; dj <= 2 && top; dj++) for (let di = -2; di <= 2; di++) if (heightG[(j + dj) * G + i + di] > h) { top = false; break; }
    if (top) cand.push({ x: (i + 0.5) * GS, y: (j + 0.5) * GS, h });
  }
  cand.sort((a, b) => b.h - a.h);
  for (const c of cand) {
    if (peaks.length >= islets.length + 16) break;
    if (peaks.some((p) => Math.hypot(p.x - c.x, p.y - c.y) < 480)) continue;
    peaks.push({ x: c.x, y: c.y, r: 50 });
  }
  tries = 0;
  while (towns.length < 26 && tries++ < 8000) {
    const x = rnd() * W, y = rnd() * W;
    if (!coastal(x, y)) continue;
    if (towns.some((t) => Math.hypot(t.x - x, t.y - y) < 500)) continue;
    if (peaks.some((p) => Math.hypot(p.x - x, p.y - y) < 160)) continue;
    towns.push({ x, y });
  }
}

let mapCanvas, miniBase;
function renderMap() {
  const MS = MOBILE ? 900 : 1400, k = W / MS;
  mapCanvas = document.createElement('canvas'); mapCanvas.width = mapCanvas.height = MS;
  const g = mapCanvas.getContext('2d'), img = g.createImageData(MS, MS), d = img.data;
  const deep = [6, 30, 78], mid = [16, 84, 150], shallow = [58, 196, 206], warmC = [20, 158, 168];
  const sand = [230, 214, 160], grass = [78, 168, 74], forest = [30, 104, 52], rock = [118, 108, 98], snow = [244, 246, 250];
  for (let j = 0; j < MS; j++) for (let i = 0; i < MS; i++) {
    const x = (i + 0.5) * k, y = (j + 0.5) * k;
    const h = hAt(x, y), grain = (hash(i, j, 3) - 0.5) * 10;
    let c;
    if (h < TH) {
      const dep = TH - h;
      c = mix(shallow, mid, clamp(dep / 0.035, 0, 1));
      c = mix(c, deep, clamp((dep - 0.035) / 0.18, 0, 1));
      const w = smooth(TW, TW + 0.05, tAt(x, y));
      c = mix(c, warmC, 0.5 * w);
    } else {
      const e = h - TH;
      if (e < 0.01) c = sand;
      else if (e < 0.1) c = mix(grass, forest, (e - 0.01) / 0.09);
      else if (e < 0.14) c = mix(forest, rock, (e - 0.1) / 0.04);
      else c = mix(rock, snow, clamp((e - 0.14) / 0.03, 0, 1));
      const sh = (h - hAt(x + k * 2, y + k * 2)) * 900;
      c = [c[0] + sh, c[1] + sh, c[2] + sh];
    }
    const o = (j * MS + i) * 4;
    d[o] = c[0] + grain; d[o + 1] = c[1] + grain; d[o + 2] = c[2] + grain; d[o + 3] = 255;
  }
  g.putImageData(img, 0, 0);
  // montañas
  for (const p of peaks) {
    const x = p.x / k, y = p.y / k, r = p.r / k * 1.25;
    const gr = g.createRadialGradient(x - r * 0.2, y - r * 0.2, 0, x, y, r);
    gr.addColorStop(0, '#ffffff'); gr.addColorStop(0.25, '#d9d6d0'); gr.addColorStop(0.55, '#7d7166'); gr.addColorStop(1, 'rgba(70,62,52,0)');
    g.fillStyle = gr; g.beginPath(); g.arc(x, y, r, 0, Math.PI * 2); g.fill();
    g.strokeStyle = 'rgba(60,50,40,.45)'; g.lineWidth = 1;
    for (let a = 0; a < 6; a++) {
      const ang = a * 1.047 + p.x;
      g.beginPath(); g.moveTo(x + Math.cos(ang) * r * 0.15, y + Math.sin(ang) * r * 0.15);
      g.lineTo(x + Math.cos(ang + 0.2) * r * 0.85, y + Math.sin(ang + 0.2) * r * 0.85); g.stroke();
    }
  }
  miniBase = document.createElement('canvas'); miniBase.width = miniBase.height = 150;
  miniBase.getContext('2d').drawImage(mapCanvas, 0, 0, 150, 150);
}

// ───────────────────────── sprites ─────────────────────────
function makeCanvas(s) { const c = document.createElement('canvas'); c.width = c.height = s; return [c, c.getContext('2d')]; }
function puff(g, x, y, r, a) {
  const gr = g.createRadialGradient(x, y, 0, x, y, r);
  gr.addColorStop(0, `rgba(255,255,255,${a})`); gr.addColorStop(1, 'rgba(255,255,255,0)');
  g.fillStyle = gr; g.beginPath(); g.arc(x, y, r, 0, Math.PI * 2); g.fill();
}
function makeStorm() {
  const S = 256, [c, g] = makeCanvas(S), H = S / 2;
  g.translate(H, H);
  puff(g, 0, 0, H, 0.35);
  const rnd = mulberry(99);
  for (let arm = 0; arm < 4; arm++) {
    for (let t = 0; t <= 1; t += 0.008) {
      const ang = arm * Math.PI / 2 + t * 4.6, rad = H * (0.08 + t * 0.82);
      const jit = (rnd() - 0.5) * H * 0.06;
      puff(g, Math.cos(ang) * (rad + jit), Math.sin(ang) * (rad + jit), H * (0.07 + 0.11 * (1 - t)), 0.16 * (1 - t * 0.5));
    }
  }
  puff(g, 0, 0, H * 0.32, 0.8);
  g.globalCompositeOperation = 'destination-out';
  const eye = g.createRadialGradient(0, 0, 0, 0, 0, H * 0.075);
  eye.addColorStop(0, 'rgba(0,0,0,1)'); eye.addColorStop(0.6, 'rgba(0,0,0,.9)'); eye.addColorStop(1, 'rgba(0,0,0,0)');
  g.fillStyle = eye; g.beginPath(); g.arc(0, 0, H * 0.075, 0, Math.PI * 2); g.fill();
  return c;
}
function makeSprites() {
  const sp = {};
  const draw = (k, fn) => { const [c, g] = makeCanvas(64); g.translate(32, 32); fn(g); sp[k] = c; };
  draw('vapor', (g) => { puff(g, 0, 0, 30, 0.95); puff(g, -10, 6, 18, 0.7); puff(g, 10, 4, 16, 0.7); });
  draw('cloud', (g) => { puff(g, 0, 0, 30, 1); puff(g, -12, 8, 20, 0.9); puff(g, 12, -6, 20, 0.9); puff(g, 0, 0, 12, 1); });
  draw('boat', (g) => {
    g.fillStyle = '#8a5a2b'; g.beginPath(); g.ellipse(0, 0, 28, 11, 0, 0, Math.PI * 2); g.fill();
    g.fillStyle = '#fff'; g.beginPath(); g.moveTo(-12, -2); g.lineTo(18, -2); g.lineTo(-6, -22); g.closePath(); g.fill();
    g.fillStyle = '#ff5a5a'; g.fillRect(-6, -3, 6, 6);
  });
  draw('ship', (g) => {
    g.fillStyle = '#3b4656'; g.beginPath(); g.moveTo(-30, -10); g.lineTo(22, -10); g.lineTo(31, 0); g.lineTo(22, 10); g.lineTo(-30, 10); g.closePath(); g.fill();
    const cols = ['#e04848', '#3d8bfd', '#f5b829', '#2fb57a', '#e04848', '#3d8bfd'];
    cols.forEach((cl, i) => { g.fillStyle = cl; g.fillRect(-24 + i * 7.5, -7, 6.5, 6); g.fillStyle = cols[(i + 2) % 6]; g.fillRect(-24 + i * 7.5, 1, 6.5, 6); });
    g.fillStyle = '#fff'; g.fillRect(-29, -8, 5, 16);
  });
  draw('platform', (g) => {
    g.fillStyle = '#5c6470'; g.fillRect(-26, -26, 52, 52);
    g.fillStyle = '#868f9c'; g.fillRect(-20, -20, 40, 40);
    g.fillStyle = '#ffcc33'; g.fillRect(-20, -20, 14, 14);
    g.strokeStyle = '#2b2f36'; g.lineWidth = 3; g.beginPath(); g.moveTo(-20, 20); g.lineTo(20, -20); g.stroke();
    g.fillStyle = '#ff7b22'; g.beginPath(); g.arc(18, 18, 7, 0, Math.PI * 2); g.fill();
    g.fillStyle = '#ffe06a'; g.beginPath(); g.arc(18, 18, 3.5, 0, Math.PI * 2); g.fill();
  });
  draw('palm', (g) => {
    g.fillStyle = 'rgba(0,0,0,.2)'; g.beginPath(); g.arc(4, 4, 24, 0, Math.PI * 2); g.fill();
    for (let i = 0; i < 7; i++) {
      g.save(); g.rotate(i * 0.9); g.fillStyle = i % 2 ? '#2e9c3f' : '#45c157';
      g.beginPath(); g.ellipse(14, 0, 16, 6, 0, 0, Math.PI * 2); g.fill(); g.restore();
    }
    g.fillStyle = '#7a5130'; g.beginPath(); g.arc(0, 0, 5, 0, Math.PI * 2); g.fill();
  });
  draw('house', (g) => {
    g.fillStyle = 'rgba(0,0,0,.25)'; g.fillRect(-20, -16, 44, 38);
    g.fillStyle = '#c4502f'; g.fillRect(-23, -20, 44, 38);
    g.fillStyle = '#e06a42'; g.fillRect(-23, -20, 44, 19);
    g.strokeStyle = '#7d2f19'; g.lineWidth = 2; g.beginPath(); g.moveTo(-23, -1); g.lineTo(21, -1); g.stroke();
  });
  draw('hotel', (g) => {
    g.fillStyle = 'rgba(0,0,0,.25)'; g.fillRect(-24, -24, 54, 54);
    g.fillStyle = '#f2efe6'; g.fillRect(-28, -28, 54, 54);
    g.fillStyle = '#d8d2c2'; for (let i = 0; i < 4; i++) g.fillRect(-24 + i * 13, -24, 9, 22);
    g.fillStyle = '#3cc4e0'; g.beginPath(); g.ellipse(0, 14, 18, 8, 0, 0, Math.PI * 2); g.fill();
  });
  draw('lighthouse', (g) => {
    g.fillStyle = 'rgba(0,0,0,.25)'; g.beginPath(); g.arc(4, 4, 22, 0, Math.PI * 2); g.fill();
    g.fillStyle = '#fff'; g.beginPath(); g.arc(0, 0, 22, 0, Math.PI * 2); g.fill();
    g.strokeStyle = '#e03b3b'; g.lineWidth = 6; g.beginPath(); g.arc(0, 0, 15, 0, Math.PI * 2); g.stroke();
    g.fillStyle = '#ffe873'; g.beginPath(); g.arc(0, 0, 7, 0, Math.PI * 2); g.fill();
  });
  return sp;
}

// ───────────────────────── estado ─────────────────────────
const canvas = document.getElementById('c');
const ctx = canvas.getContext('2d');
const $ = (id) => document.getElementById(id);
let DPR = 1, now = 0;
let STORM, SPR;
const objs = [];
const respawnQ = [];
const storms = [];
let player = null;
let all = [];
const particles = [], flashes = [];
const cam = { x: W / 2, y: W / 2, s: 0.6 };
const input = { mx: 0, my: 0, joy: null, dir: { x: 0, y: 0 }, mouse: !MOBILE };
const game = { state: 'menu', warmMul: 1, decayMul: 1, event: null, eventEnd: 0, nextEvent: 50, nextPop: 20, popTarget: 17, combo: 0, comboT: 0 };
let usedNames = new Set();

class Storm {
  constructor(name, color, bot) {
    this.name = name; this.color = color; this.bot = bot; this.cells = [];
    this.tx = 0; this.ty = 0; this.born = now; this.best = 0; this.bestCat = 0; this.kills = 0;
    this.ai = bot ? { aggr: 0.3 + Math.random() * 0.7, caution: 0.5 + Math.random() * 0.5, landOk: 0.3 + Math.random() * 0.6, next: 0, wx: 0, wy: 0 } : null;
  }
  get mass() { let s = 0; for (const c of this.cells) s += c.m; return s; }
  center() {
    let x = 0, y = 0, m = 0;
    for (const c of this.cells) { x += c.x * c.m; y += c.y * c.m; m += c.m; }
    return m ? { x: x / m, y: y / m } : { x: this.tx, y: this.ty };
  }
  biggest() { let b = null; for (const c of this.cells) if (!b || c.m > b.m) b = c; return b; }
}
function newCell(o, x, y, m) {
  const c = { o, x, y, m, vx: 0, vy: 0, mergeAt: 0, rot: Math.random() * 6, popCd: 0, shield: 0, dead: false, r: radius(m) };
  o.cells.push(c); return c;
}

// ───────────────────────── objetos ─────────────────────────
function freeSpot(x, y, pad) {
  for (const c of all) { const r = c.r + pad; if (Math.abs(c.x - x) < r && Math.abs(c.y - y) < r && Math.hypot(c.x - x, c.y - y) < r) return false; }
  return true;
}
function placeObj(kind) {
  const K = KINDS[kind];
  for (let t = 0; t < 60; t++) {
    let x, y;
    if (K.where === 'town' && Math.random() < 0.8) {
      const tw = towns[(Math.random() * towns.length) | 0];
      const a = Math.random() * 6.28, d = Math.sqrt(Math.random()) * 230;
      x = tw.x + Math.cos(a) * d; y = tw.y + Math.sin(a) * d;
    } else { x = 60 + Math.random() * (W - 120); y = 60 + Math.random() * (W - 120); }
    const L = isLand(x, y);
    if (K.where === 'sea' ? L : !L) continue;
    if (K.where === 'coast' && !coastal(x, y)) continue;
    if (L && peaks.some((p) => Math.hypot(p.x - x, p.y - y) < p.r + K.r)) continue;
    if (!freeSpot(x, y, 40)) continue;
    const ang = Math.random() * 6.28;
    const o = { k: kind, K, x, y, rot: kind === 'house' || kind === 'hotel' ? (Math.random() < 0.5 ? 0 : 1.57) : ang, vx: 0, vy: 0, alive: true, suck: null, owner: null, t: now, born: now };
    if (K.move) { o.vx = Math.cos(ang) * K.move; o.vy = Math.sin(ang) * K.move; }
    objs.push(o); return o;
  }
  return null;
}
function populate() { for (const k in KINDS) for (let i = 0; i < (KINDS[k].n || 0); i++) placeObj(k); }

// ───────────────────────── tormentas ─────────────────────────
function pickName() {
  const free = NAMES.filter((n) => !usedNames.has(n));
  const n = free.length ? free[(Math.random() * free.length) | 0] : NAMES[(Math.random() * NAMES.length) | 0] + ' II';
  usedNames.add(n); return n;
}
function randomSea(warm, awayFrom, minD) {
  for (let t = 0; t < 400; t++) {
    const x = 500 + Math.random() * (W - 1000), y = 500 + Math.random() * (W - 1000);
    if (isLand(x, y)) continue;
    if (warm && t < 300 && warmAt(x, y) < 0.5) continue;
    if (awayFrom && Math.hypot(awayFrom.x - x, awayFrom.y - y) < minD) continue;
    let ok = true;
    for (const c of all) if (c.m > 30 && Math.hypot(c.x - x, c.y - y) < c.r + 500) { ok = false; break; }
    if (ok) return { x, y };
  }
  return { x: W / 2, y: W / 2 };
}
function addBot(silent) {
  const o = new Storm(pickName(), COLORS[(Math.random() * COLORS.length) | 0], true);
  const p = randomSea(true, player && player.cells.length ? player.center() : null, 900);
  const m = START_M + Math.random() * Math.random() * 160;
  const c = newCell(o, p.x, p.y, m); c.shield = now + 3;
  o.tx = p.x; o.ty = p.y;
  storms.push(o);
  if (!silent) feed(`🌀 <b style="color:${o.color}">${o.name}</b> se formó`);
  return o;
}
function removeStorm(o) {
  const i = storms.indexOf(o); if (i >= 0) storms.splice(i, 1);
  usedNames.delete(o.name);
}

function split(o) {
  const list = [...o.cells].sort((a, b) => b.m - a.m);
  let did = false;
  for (const c of list) {
    if (o.cells.length >= MAX_CELLS) break;
    if (c.m < SPLIT_MIN) continue;
    let dx = o.tx - c.x, dy = o.ty - c.y, d = Math.hypot(dx, dy);
    if (d < 1) { const a = Math.random() * 6.28; dx = Math.cos(a); dy = Math.sin(a); d = 1; }
    dx /= d; dy /= d;
    c.m /= 2; c.r = radius(c.m);
    const n = newCell(o, c.x + dx * c.r * 0.5, c.y + dy * c.r * 0.5, c.m);
    const v = 620 + n.r * 3;
    n.vx = dx * v; n.vy = dy * v; n.rot = c.rot;
    c.mergeAt = n.mergeAt = now + mergeTime(c.m);
    did = true;
  }
  if (did && o === player) sfx.throw();
  return did;
}
function eject(o) {
  let did = false;
  for (const c of o.cells) {
    if (c.m < EJECT_MIN) continue;
    let dx = o.tx - c.x, dy = o.ty - c.y, d = Math.hypot(dx, dy);
    if (d < 1) { dx = 1; dy = 0; d = 1; }
    dx /= d; dy /= d;
    c.m -= EJECT_COST; c.r = radius(c.m);
    const a = (Math.random() - 0.5) * 0.25;
    const ex = dx * Math.cos(a) - dy * Math.sin(a), ey = dx * Math.sin(a) + dy * Math.cos(a);
    objs.push({ k: 'cloud', K: KINDS.cloud, x: c.x + ex * (c.r + 12), y: c.y + ey * (c.r + 12), rot: Math.random() * 6, vx: ex * 640, vy: ey * 640, alive: true, suck: null, owner: o, t: now, born: now });
    did = true;
  }
  if (did && o === player) sfx.bombPick();
}
function popOnPeak(c, p) {
  const o = c.o;
  c.popCd = now + 2.5;
  const slots = MAX_CELLS - o.cells.length;
  if (slots <= 0) {
    c.m *= 0.85; c.r = radius(c.m);
    if (o === player) banner('⛰️ La montaña te frenó', '−15 %');
    return;
  }
  const n = Math.min(slots, 6 + Math.floor(c.m / 200));
  const piece = (c.m * 0.5) / n;
  c.m *= 0.5; c.r = radius(c.m);
  c.mergeAt = now + mergeTime(c.m);
  for (let i = 0; i < n; i++) {
    const a = (i / n) * 6.28 + Math.random() * 0.4;
    const k = newCell(o, c.x + Math.cos(a) * c.r * 0.5, c.y + Math.sin(a) * c.r * 0.5, piece);
    const v = 520 + Math.random() * 200;
    k.vx = Math.cos(a) * v; k.vy = Math.sin(a) * v; k.mergeAt = now + mergeTime(c.m);
  }
  burst(p.x, p.y, '#cfc6b8', 30, c.r);
  if (o === player) { sfx.boom(); banner('⛰️ ¡LA MONTAÑA TE DESPEDAZÓ!', 'Juntate antes de que te coman'); shake = 0.6; }
}

// ───────────────────────── IA ─────────────────────────
function think(o) {
  const big = o.biggest(); if (!big) return;
  const ai = o.ai;
  const cx = big.x, cy = big.y;
  // amenazas
  let fx = 0, fy = 0, threat = 0;
  for (const e of all) {
    if (e.o === o || e.m < big.m * EAT * 0.95) continue;
    const canSplit = e.m / 2 > big.m * EAT && e.o.cells.length < MAX_CELLS;
    const reach = e.r + big.r + 150 + (canSplit ? 240 + e.r : 0);
    const dx = cx - e.x, dy = cy - e.y, d = Math.hypot(dx, dy);
    if (d < reach) { const w = (reach - d) / reach; fx += dx / (d || 1) * w; fy += dy / (d || 1) * w; threat = Math.max(threat, w); }
  }
  if (threat > 0.15 * (1.4 - ai.caution)) {
    const len = Math.hypot(fx, fy) || 1;
    let ang = Math.atan2(fy / len, fx / len);
    for (let t = 0; t < 6; t++) {
      const tx = cx + Math.cos(ang) * 500, ty = cy + Math.sin(ang) * 500;
      if (!isLand(tx, ty) && tx > 100 && ty > 100 && tx < W - 100 && ty < W - 100) break;
      ang += (t % 2 ? -1 : 1) * 0.5 * (t + 1);
    }
    o.tx = cx + Math.cos(ang) * 500; o.ty = cy + Math.sin(ang) * 500;
    if (threat > 0.8 && big.m > 60 && Math.random() < 0.15) eject(o);
    return;
  }
  // presa
  let best = null, bs = 0;
  for (const e of all) {
    if (e.o === o || e.shield > now || big.m < e.m * EAT * 1.05) continue;
    if (e.o === player && now - player.born < 15) continue;
    const d = Math.hypot(e.x - cx, e.y - cy);
    if (d > 900) continue;
    const s = (e.m / (d + 80)) * ai.aggr * 3;
    if (s > bs) { bs = s; best = e; }
  }
  if (best) {
    const d = Math.hypot(best.x - cx, best.y - cy);
    if (o.cells.length <= 2 && big.m / 2 >= best.m * EAT * 1.1 && d < 200 + big.r * 1.6 && ai.aggr > 0.55 && !peakNear(best.x, best.y, big.m / 2)) {
      o.tx = best.x; o.ty = best.y; split(o); return;
    }
  }
  // comida
  for (const ob of objs) {
    if (!ob.alive || ob.suck || big.r < ob.K.need) continue;
    const dx = ob.x - cx, dy = ob.y - cy;
    if (Math.abs(dx) > 800 || Math.abs(dy) > 800) continue;
    const d = Math.hypot(dx, dy);
    let s = ob.K.m / (d + 60);
    if (ob.K.where === 'land' || ob.K.where === 'town' || ob.K.where === 'coast') s *= ai.landOk;
    if (big.m >= PEAK_POP && peakNear(ob.x, ob.y, big.m)) continue;
    if (s > bs) { bs = s; best = ob; }
  }
  if (best) { o.tx = best.x; o.ty = best.y; }
  else {
    if (!ai.wx || Math.hypot(ai.wx - cx, ai.wy - cy) < 150 || Math.random() < 0.01) { const p = randomSea(true); ai.wx = p.x; ai.wy = p.y; }
    o.tx = ai.wx; o.ty = ai.wy;
  }
  // esquivar montañas
  if (big.m >= PEAK_POP) for (const p of peaks) {
    const dx = cx - p.x, dy = cy - p.y, d = Math.hypot(dx, dy);
    if (d < big.r + p.r + 160) { o.tx = cx + dx / d * 400; o.ty = cy + dy / d * 400; break; }
  }
}
function peakNear(x, y, m) {
  if (m < PEAK_POP) return false;
  const r = radius(m);
  return peaks.some((p) => Math.hypot(p.x - x, p.y - y) < r + p.r + 60);
}

// ───────────────────────── reglas ─────────────────────────
function eatCell(a, b) {
  a.m += b.m; a.r = radius(a.m); b.dead = true;
  const o = b.o; o.cells.splice(o.cells.indexOf(b), 1);
  burst(b.x, b.y, o.color, 14 + Math.min(30, b.r * 0.4), b.r);
  if (a.o === player) { sfx.hole(); if (!o.cells.length) { player.kills++; feed(`🌀 Te tragaste a <b style="color:${o.color}">${o.name}</b>`); banner(`🌀 ¡TE TRAGASTE A ${o.name.toUpperCase()}!`, `+${Math.round(b.m)} de masa`); } }
  else if (o === player) { shake = 0.4; }
  if (!o.cells.length) dieStorm(o, a.o);
}
function dieStorm(o, by) {
  if (o === player) { die(by ? `Te tragó <b style="color:${by.color}">${by.name}</b>` : 'Te disipaste'); return; }
  if (by && by !== player) feed(`<b style="color:${by.color}">${by.name}</b> se tragó a <b style="color:${o.color}">${o.name}</b>`);
  removeStorm(o);
}

function eatObjects(c) {
  for (const ob of objs) {
    if (!ob.alive || ob.suck) continue;
    const dx = ob.x - c.x; if (dx > c.r || dx < -c.r) continue;
    const dy = ob.y - c.y; if (dy > c.r || dy < -c.r) continue;
    if (dx * dx + dy * dy > c.r * c.r * 0.85 || c.r < ob.K.need) continue;
    if (ob.owner === c.o && now - ob.t < 0.6) continue;
    ob.suck = { c, t: 0, ang: Math.atan2(dy, dx), d: Math.hypot(dx, dy) };
    c.m += ob.K.m; c.r = radius(c.m);
    if (ob.k !== 'cloud') respawnQ.push({ k: ob.k, at: now + 15 + Math.random() * 25 });
    if (c.o === player) {
      game.combo = now - game.comboT < 1.2 ? game.combo + 1 : 1; game.comboT = now;
      if (ob.K.m >= 10) { sfx.gold(); popText(ob.x, ob.y, `+${ob.K.m}`); } else sfx.eat(game.combo, c.r / 20);
    }
  }
}

function step(dt) {
  all = [];
  for (const o of storms) for (const c of o.cells) all.push(c);

  // timers de IA y población
  for (const o of storms) if (o.bot && now >= o.ai.next) { o.ai.next = now + 0.18 + Math.random() * 0.15; think(o); }
  if (now >= game.nextPop) {
    game.nextPop = now + 18 + Math.random() * 25;
    if (Math.random() < 0.15) game.popTarget = clamp(game.popTarget + (Math.random() < 0.5 ? -2 : 2), 12, 22);
    const bots = storms.filter((o) => o.bot);
    if (bots.length < game.popTarget) addBot(false);
    else if (bots.length > game.popTarget || Math.random() < 0.3) {
      const pc = player && player.cells.length ? player.center() : { x: -9e9, y: -9e9 };
      const leaver = bots.find((o) => o.mass < 300 && Math.hypot(o.center().x - pc.x, o.center().y - pc.y) > 1400);
      if (leaver) { feed(`💨 <b style="color:${leaver.color}">${leaver.name}</b> se disipó`); removeStorm(leaver); }
    }
  }
  const bots = storms.filter((o) => o.bot).length;
  if (bots < game.popTarget - 3) addBot(false);

  // movimiento
  for (const o of storms) {
    for (const c of o.cells) {
      const L = isLand(c.x, c.y);
      let dx = o.tx - c.x, dy = o.ty - c.y; const d = Math.hypot(dx, dy);
      const s = speedOf(c.m) * Math.min(1, d / (c.r * 0.4 + 25)) * (L ? 0.82 : 1);
      if (d > 0.5) { c.x += dx / d * s * dt; c.y += dy / d * s * dt; }
      c.x += c.vx * dt; c.y += c.vy * dt;
      const fr = Math.exp(-dt * 3.5); c.vx *= fr; c.vy *= fr;
      c.x = clamp(c.x, 0, W); c.y = clamp(c.y, 0, W);
      c.rot += dt * (0.5 + 3.5 / Math.sqrt(c.m));
      // clima
      if (L) { if (c.m > START_M) c.m = Math.max(START_M, c.m - c.m * 0.035 * dt); }
      else c.m += dt * (0.2 + c.m * 0.0035) * warmAt(c.x, c.y) * game.warmMul;
      if (c.m > 150) c.m -= dt * c.m * 0.0018 * game.decayMul;
      c.r = radius(c.m);
      // montañas
      if (c.m >= PEAK_POP && now > c.popCd) for (const p of peaks) {
        const ex = p.x - c.x, ey = p.y - c.y;
        if (Math.abs(ex) < c.r && Math.abs(ey) < c.r && ex * ex + ey * ey < (c.r * 0.8) ** 2) { popOnPeak(c, p); break; }
      }
    }
    // celdas propias: empujar o fusionar
    const cs = o.cells;
    for (let i = 0; i < cs.length; i++) for (let j = i + 1; j < cs.length; j++) {
      const a = cs[i], b = cs[j]; if (a.dead || b.dead) continue;
      const dx = b.x - a.x, dy = b.y - a.y, d = Math.hypot(dx, dy) || 0.01, rr = a.r + b.r;
      if (now < a.mergeAt || now < b.mergeAt) {
        if (d < rr) { const push = (rr - d) * Math.min(1, dt * 8), wa = b.m / (a.m + b.m); a.x -= dx / d * push * wa; a.y -= dy / d * push * wa; b.x += dx / d * push * (1 - wa); b.y += dy / d * push * (1 - wa); }
      } else if (d < Math.max(a.r, b.r) * 0.6) {
        const [big, small] = a.m >= b.m ? [a, b] : [b, a];
        big.m += small.m; big.r = radius(big.m); small.dead = true;
      }
    }
    if (cs.some((c) => c.dead)) o.cells = cs.filter((c) => !c.dead);
  }
  all = [];
  for (const o of storms) for (const c of o.cells) all.push(c);

  // comerse entre tormentas
  all.sort((a, b) => b.m - a.m);
  for (let i = 0; i < all.length; i++) {
    const a = all[i]; if (a.dead) continue;
    for (let j = i + 1; j < all.length; j++) {
      const b = all[j]; if (b.dead || b.o === a.o || b.shield > now || a.shield > now) continue;
      if (a.m < b.m * EAT) continue;
      const dx = a.x - b.x, dy = a.y - b.y;
      if (Math.abs(dx) > a.r || Math.abs(dy) > a.r) continue;
      if (Math.hypot(dx, dy) < a.r - b.r * 0.35) eatCell(a, b);
    }
  }
  all = all.filter((c) => !c.dead);
  for (const c of all) eatObjects(c);

  // objetos
  for (const ob of objs) {
    if (!ob.alive) continue;
    if (ob.suck) {
      const s = ob.suck; s.t += dt;
      if (s.t >= 0.5 || s.c.dead) { ob.alive = false; continue; }
      const p = s.t / 0.5, a = s.ang + p * 7, d = s.d * (1 - p);
      ob.x = s.c.x + Math.cos(a) * d; ob.y = s.c.y + Math.sin(a) * d; ob.rot += dt * 12;
      continue;
    }
    if (ob.k === 'cloud') {
      ob.x += ob.vx * dt; ob.y += ob.vy * dt; const fr = Math.exp(-dt * 4); ob.vx *= fr; ob.vy *= fr;
      ob.x = clamp(ob.x, 0, W); ob.y = clamp(ob.y, 0, W);
      if (now - ob.born > 60) ob.alive = false;
    } else if (ob.K.move) {
      const nx = ob.x + ob.vx * dt, ny = ob.y + ob.vy * dt;
      if (isLand(nx + ob.vx * 0.6, ny + ob.vy * 0.6) || nx < 50 || ny < 50 || nx > W - 50 || ny > W - 50) {
        const a = Math.atan2(ob.vy, ob.vx) + Math.PI * (0.6 + Math.random() * 0.8), sp = ob.K.move;
        ob.vx = Math.cos(a) * sp; ob.vy = Math.sin(a) * sp;
      } else { ob.x = nx; ob.y = ny; }
      ob.rot = Math.atan2(ob.vy, ob.vx);
    }
  }
  if (objs.length > 400 && Math.random() < 0.05) { let w = 0; for (const ob of objs) if (ob.alive) objs[w++] = ob; objs.length = w; }
  for (let i = respawnQ.length - 1; i >= 0; i--) if (now >= respawnQ[i].at) { const q = respawnQ.splice(i, 1)[0]; if (!placeObj(q.k)) respawnQ.push({ k: q.k, at: now + 5 }); }

  worldEvents();
  for (const o of storms) { const m = o.mass; if (m > o.best) o.best = m; }
}

function worldEvents() {
  if (game.event && now >= game.eventEnd) { game.event = null; game.warmMul = 1; game.decayMul = 1; $('event').classList.add('hidden'); }
  if (now < game.nextEvent) return;
  game.nextEvent = now + 60 + Math.random() * 40;
  const r = Math.random(), el = $('event');
  el.className = '';
  if (r < 0.4) {
    game.event = 'nino'; game.eventEnd = now + 25; game.warmMul = 3.5;
    el.textContent = '🌡️ EL NIÑO · el mar hierve'; banner('🌡️ ¡EL NIÑO!', 'El agua caliente te da el triple');
  } else if (r < 0.7) {
    game.event = 'frio'; game.eventEnd = now + 20; game.warmMul = 0; game.decayMul = 3;
    el.className = 'cold'; el.textContent = '❄️ FRENTE FRÍO · los grandes se debilitan'; banner('❄️ FRENTE FRÍO', 'Los huracanes grandes pierden fuerza');
  } else {
    game.event = 'lluvia'; game.eventEnd = now + 12;
    el.className = 'rain'; el.textContent = '🌧️ TEMPORADA DE LLUVIAS';
    banner('🌧️ TEMPORADA DE LLUVIAS', 'Vapor por todo el mar');
    for (let i = 0; i < 450; i++) placeObj('vapor');
  }
  sfx.event();
}

// ───────────────────────── jugador ─────────────────────────
function spawnPlayer() {
  const name = ($('nameIn').value || '').trim() || 'Vos';
  player = new Storm(name, PLAYER_COLOR, false); bestRank = 99;
  const p = randomSea(true, null, 0);
  const c = newCell(player, p.x, p.y, START_M); c.shield = now + 4;
  player.tx = p.x; player.ty = p.y;
  storms.push(player);
  cam.x = p.x; cam.y = p.y;
  game.state = 'play';
  $('hud').classList.remove('hidden');
  $('dead').classList.add('hidden');
}
function die(why) {
  const o = player;
  removeStorm(o);
  game.state = 'dead';
  sfx.death();
  $('deadWhy').innerHTML = why;
  const t = Math.round(now - o.born);
  $('deadStats').innerHTML = `<div><b>${CATS[o.bestCat][0]}</b>Máxima categoría</div><div><b>${Math.round(windOf(o.best))} km/h</b>Viento máximo</div>`
    + `<div><b>${Math.round(o.best)}</b>Masa máxima</div><div><b>${o.kills}</b>Tormentas tragadas</div><div><b>${Math.floor(t / 60)}:${String(t % 60).padStart(2, '0')}</b>Tiempo vivo</div><div><b>${rankOf(o)}</b>Mejor puesto</div>`;
  setTimeout(() => { if (game.state === 'dead') $('dead').classList.remove('hidden'); }, 900);
}
let bestRank = 99;
function rankOf() { return bestRank === 99 ? '—' : `#${bestRank}`; }

// ───────────────────────── efectos ─────────────────────────
let shake = 0;
function burst(x, y, color, n, r) {
  for (let i = 0; i < n; i++) {
    const a = Math.random() * 6.28, v = 60 + Math.random() * 220;
    particles.push({ x: x + Math.cos(a) * r * 0.3, y: y + Math.sin(a) * r * 0.3, vx: Math.cos(a) * v, vy: Math.sin(a) * v, life: 0.6 + Math.random() * 0.5, t: 0, color, s: 3 + Math.random() * 5 });
  }
}
const pops = [];
function popText(x, y, txt) { pops.push({ x, y, txt, t: 0 }); }
let bannerT = 0;
function banner(title, small) {
  const b = $('banner'); b.innerHTML = `${title}${small ? `<small>${small}</small>` : ''}`; b.classList.add('show');
  clearTimeout(bannerT); bannerT = setTimeout(() => b.classList.remove('show'), 2200);
}
function feed(html) {
  const f = $('feed'), d = document.createElement('div'); d.innerHTML = html; f.prepend(d);
  while (f.children.length > 5) f.lastChild.remove();
  setTimeout(() => d.remove(), 5200);
}

// ───────────────────────── render ─────────────────────────
function resize() {
  DPR = Math.min(window.devicePixelRatio || 1, MOBILE ? 1.5 : 2);
  canvas.width = Math.round(innerWidth * DPR); canvas.height = Math.round(innerHeight * DPR);
}
function updateCamera(dt) {
  let tx = cam.x, ty = cam.y, mass = 40, n = 1;
  if (player && player.cells.length) { const c = player.center(); tx = c.x; ty = c.y; mass = player.mass; n = player.cells.length; }
  const k = 1 - Math.exp(-dt * 6);
  cam.x += (tx - cam.x) * k; cam.y += (ty - cam.y) * k;
  const view = (MOBILE ? 520 : 720) + Math.sqrt(mass) * 26 + Math.min(10, n - 1) * 45;
  const ts = Math.sqrt(innerWidth * innerHeight) / view;
  cam.s += (ts - cam.s) * (1 - Math.exp(-dt * 2.5));
}
function draw(dt) {
  const sw = innerWidth, sh = innerHeight, s = cam.s;
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.fillStyle = '#041a33'; ctx.fillRect(0, 0, canvas.width, canvas.height);
  let ox = 0, oy = 0;
  if (shake > 0) { shake = Math.max(0, shake - dt); ox = (Math.random() - 0.5) * shake * 30; oy = (Math.random() - 0.5) * shake * 30; }
  ctx.setTransform(DPR * s, 0, 0, DPR * s, DPR * (sw / 2 - cam.x * s + ox), DPR * (sh / 2 - cam.y * s + oy));
  const x0 = cam.x - sw / 2 / s - 60, x1 = cam.x + sw / 2 / s + 60, y0 = cam.y - sh / 2 / s - 60, y1 = cam.y + sh / 2 / s + 60;
  const vis = (x, y, r) => x + r > x0 && x - r < x1 && y + r > y0 && y - r < y1;

  // mapa
  const k = mapCanvas.width / W;
  const ax = clamp(x0, 0, W), ay = clamp(y0, 0, W), bx = clamp(x1, 0, W), by = clamp(y1, 0, W);
  if (bx > ax && by > ay) ctx.drawImage(mapCanvas, ax * k, ay * k, (bx - ax) * k, (by - ay) * k, ax, ay, bx - ax, by - ay);
  // olas que brillan
  ctx.globalAlpha = 0.12; ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 2 / s;
  const step = 220, gx0 = Math.floor(x0 / step), gy0 = Math.floor(y0 / step);
  ctx.beginPath();
  for (let gx = gx0; gx * step < x1; gx++) for (let gy = gy0; gy * step < y1; gy++) {
    const h = hash(gx, gy, 5); if (h > 0.45) continue;
    const px = gx * step + h * step * 2, py = gy * step + hash(gx, gy, 6) * step, ph = Math.sin(now * 1.5 + h * 30);
    if (ph < 0 || isLand(px, py)) continue;
    const L = 14 + ph * 16;
    ctx.moveTo(px - L, py); ctx.quadraticCurveTo(px, py - 5, px + L, py);
  }
  ctx.stroke(); ctx.globalAlpha = 1;
  ctx.strokeStyle = 'rgba(255,255,255,.35)'; ctx.lineWidth = 6 / s; ctx.strokeRect(0, 0, W, W);

  // aviso de montañas
  if (player && player.cells.length && player.biggest().m >= PEAK_POP * 0.8) {
    ctx.setLineDash([12 / s * 0.6, 10 / s * 0.6]); ctx.lineWidth = 3 / s; ctx.strokeStyle = `rgba(255,80,80,${0.5 + 0.3 * Math.sin(now * 5)})`;
    for (const p of peaks) if (vis(p.x, p.y, p.r * 2)) { ctx.beginPath(); ctx.arc(p.x, p.y, p.r * 1.3, 0, Math.PI * 2); ctx.stroke(); }
    ctx.setLineDash([]);
  }

  // objetos
  for (const ob of objs) {
    if (!ob.alive || !vis(ob.x, ob.y, ob.K.r * 2)) continue;
    let r = ob.K.r;
    if (ob.suck) r *= 1 - ob.suck.t / 0.5 * 0.85;
    else if (now - ob.born < 0.5) r *= (now - ob.born) / 0.5;
    if (r < 0.5) continue;
    const spr = SPR[ob.k];
    if (ob.k === 'vapor' || ob.k === 'cloud') {
      const bob = ob.k === 'vapor' ? 1 + Math.sin(now * 2 + ob.x) * 0.08 : 1;
      ctx.drawImage(spr, ob.x - r * bob, ob.y - r * bob, r * 2 * bob, r * 2 * bob);
    } else {
      ctx.save(); ctx.translate(ob.x, ob.y); ctx.rotate(ob.rot); ctx.drawImage(spr, -r * 1.15, -r * 1.15, r * 2.3, r * 2.3); ctx.restore();
    }
  }

  // tormentas (las chicas debajo)
  const cells = all.filter((c) => vis(c.x, c.y, c.r * 1.3)).sort((a, b) => a.m - b.m);
  for (const c of cells) {
    const R = c.r * 1.22;
    ctx.globalAlpha = 0.22; ctx.fillStyle = '#001022';
    ctx.beginPath(); ctx.arc(c.x + c.r * 0.12, c.y + c.r * 0.16, c.r * 1.02, 0, Math.PI * 2); ctx.fill();
    ctx.globalAlpha = c.shield > now ? 0.45 + 0.35 * Math.sin(now * 14) : 1;
    ctx.save(); ctx.translate(c.x, c.y); ctx.rotate(-c.rot); ctx.drawImage(STORM, -R, -R, R * 2, R * 2); ctx.restore();
    ctx.globalAlpha = 0.9; ctx.strokeStyle = c.o.color; ctx.lineWidth = Math.max(2 / s, c.r * 0.05);
    ctx.beginPath(); ctx.arc(c.x, c.y, c.r, 0, Math.PI * 2); ctx.stroke();
    ctx.lineWidth = Math.max(1.5 / s, c.r * 0.025);
    ctx.beginPath(); ctx.arc(c.x, c.y, c.r * 0.11, 0, Math.PI * 2); ctx.stroke();
    ctx.globalAlpha = 1;
    if (c.m > 435 && Math.random() < dt * 2.5) flashes.push({ c, t: 0, a: Math.random() * 6.28, seed: Math.random() * 1000 });
    if (c.r * s > 16) {
      const fs = clamp(c.r * 0.3, 10 / s, 60);
      ctx.font = `800 ${fs}px 'Baloo 2', sans-serif`; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.lineWidth = fs * 0.18; ctx.strokeStyle = 'rgba(0,20,40,.75)'; ctx.fillStyle = '#fff';
      ctx.strokeText(c.o.name, c.x, c.y + c.r * 0.42); ctx.fillText(c.o.name, c.x, c.y + c.r * 0.42);
      if (c.r * s > 34) {
        const f2 = fs * 0.62; ctx.font = `700 ${f2}px 'Baloo 2', sans-serif`;
        const t = `${Math.round(c.m)}`;
        ctx.lineWidth = f2 * 0.18; ctx.strokeText(t, c.x, c.y + c.r * 0.42 + fs * 0.85); ctx.fillText(t, c.x, c.y + c.r * 0.42 + fs * 0.85);
      }
    }
  }
  // rayos
  for (let i = flashes.length - 1; i >= 0; i--) {
    const f = flashes[i]; f.t += dt;
    if (f.t > 0.14 || f.c.dead) { flashes.splice(i, 1); continue; }
    const c = f.c; ctx.strokeStyle = 'rgba(255,250,200,.95)'; ctx.lineWidth = Math.max(2 / s, c.r * 0.02);
    ctx.beginPath(); let px = c.x + Math.cos(f.a) * c.r * 0.25, py = c.y + Math.sin(f.a) * c.r * 0.25; ctx.moveTo(px, py);
    for (let j = 1; j <= 5; j++) {
      const rr = c.r * (0.25 + j * 0.12), aa = f.a + (hash(j, f.seed | 0, 9) - 0.5) * 0.6;
      ctx.lineTo(c.x + Math.cos(aa) * rr, c.y + Math.sin(aa) * rr);
    }
    ctx.stroke();
  }
  // partículas
  for (let i = particles.length - 1; i >= 0; i--) {
    const p = particles[i]; p.t += dt;
    if (p.t > p.life) { particles.splice(i, 1); continue; }
    p.x += p.vx * dt; p.y += p.vy * dt; p.vx *= 0.96; p.vy *= 0.96;
    ctx.globalAlpha = 1 - p.t / p.life; ctx.fillStyle = p.color;
    ctx.beginPath(); ctx.arc(p.x, p.y, p.s, 0, Math.PI * 2); ctx.fill();
  }
  ctx.globalAlpha = 1;
  for (let i = pops.length - 1; i >= 0; i--) {
    const p = pops[i]; p.t += dt;
    if (p.t > 1) { pops.splice(i, 1); continue; }
    const fs = 18 / s;
    ctx.globalAlpha = 1 - p.t; ctx.font = `800 ${fs}px 'Baloo 2', sans-serif`; ctx.textAlign = 'center';
    ctx.fillStyle = '#ffe066'; ctx.lineWidth = fs * 0.15; ctx.strokeStyle = 'rgba(0,0,0,.6)';
    ctx.strokeText(p.txt, p.x, p.y - p.t * 60 / s); ctx.fillText(p.txt, p.x, p.y - p.t * 60 / s);
  }
  ctx.globalAlpha = 1;
}

// ───────────────────────── HUD ─────────────────────────
let hudT = 0, miniT = 0;
const mctx = $('mini').getContext('2d');
function hud(dt) {
  hudT -= dt; miniT -= dt;
  if (!player || !player.cells.length) return;
  const m = player.mass, ci = catOf(m);
  if (ci > player.bestCat) {
    player.bestCat = ci;
    if (ci >= 2) { sfx.level(); banner(`🌀 ${CATS[ci][0].toUpperCase()}`, `${Math.round(windOf(m))} km/h`); }
  }
  if (hudT <= 0) {
    hudT = 0.25;
    $('cat').textContent = CATS[ci][0];
    $('wind').textContent = `💨 ${Math.round(windOf(m))} km/h · masa ${Math.round(m)}`;
    const nx = CATS[ci + 1];
    if (nx) {
      const w = windOf(m), a = CATS[ci][1] || 20;
      $('barFill').style.width = `${clamp((w - a) / (nx[1] - a), 0, 1) * 100}%`;
      $('next').textContent = `Siguiente: ${nx[0]} (${nx[1]} km/h)`;
    } else { $('barFill').style.width = '100%'; $('next').textContent = '🌀 Categoría máxima'; }
    const c = player.center(), z = $('zone');
    if (isLand(c.x, c.y)) { z.className = 'land'; z.textContent = '🏝️ Sobre tierra: te debilitás'; }
    else if (warmAt(c.x, c.y) > 0.5 && game.warmMul > 0) { z.className = 'warm'; z.textContent = '🌡️ Agua caliente: crecés'; }
    else { z.className = ''; z.textContent = player.cells.length > 1 ? `🌀 ${player.cells.length} pedazos` : ''; }
    const list = storms.map((o) => ({ o, m: o.mass })).sort((a, b) => b.m - a.m);
    const rank = list.findIndex((e) => e.o === player) + 1;
    bestRank = Math.min(bestRank, rank);
    let html = '';
    const top = MOBILE ? 5 : 8;
    list.slice(0, top).forEach((e, i) => { html += row(i + 1, e.o, e.m); });
    if (rank > top) html += row(rank, player, m);
    $('board').innerHTML = html;
  }
  if (miniT <= 0) {
    miniT = 0.2;
    mctx.drawImage(miniBase, 0, 0);
    const k = 150 / W;
    for (const c of all) {
      if (c.o !== player && c.m < 60) continue;
      mctx.fillStyle = c.o.color; mctx.beginPath(); mctx.arc(c.x * k, c.y * k, Math.max(1.5, c.r * k), 0, Math.PI * 2); mctx.fill();
    }
    const vw = innerWidth / cam.s * k, vh = innerHeight / cam.s * k;
    mctx.strokeStyle = '#fff'; mctx.lineWidth = 1; mctx.strokeRect(cam.x * k - vw / 2, cam.y * k - vh / 2, vw, vh);
  }
}
function row(n, o, m) {
  const me = o === player;
  return `<div class="row${me ? ' me' : ''}"><span>${n}.</span><span class="dot" style="background:${o.color}"></span><span class="nm">${o.name}</span><span class="ms">${Math.round(m)}</span></div>`;
}

// ───────────────────────── input ─────────────────────────
addEventListener('mousemove', (e) => { input.mx = e.clientX; input.my = e.clientY; input.mouse = true; });
addEventListener('keydown', (e) => {
  if (game.state !== 'play') return;
  if (e.code === 'Space') { e.preventDefault(); split(player); }
  if (e.code === 'KeyW') eject(player);
});
const joy = $('joy'), knob = $('knob');
canvas.addEventListener('touchstart', (e) => {
  input.mouse = false;
  const t = e.changedTouches[0];
  input.joy = { id: t.identifier, x: t.clientX, y: t.clientY };
  joy.style.display = 'block'; joy.style.left = `${t.clientX}px`; joy.style.top = `${t.clientY}px`;
  knob.style.transform = 'translate(0,0)';
}, { passive: true });
canvas.addEventListener('touchmove', (e) => {
  if (!input.joy) return;
  for (const t of e.changedTouches) if (t.identifier === input.joy.id) {
    let dx = t.clientX - input.joy.x, dy = t.clientY - input.joy.y; const d = Math.hypot(dx, dy), mx = 55;
    if (d > mx) { dx = dx / d * mx; dy = dy / d * mx; }
    knob.style.transform = `translate(${dx}px,${dy}px)`;
    input.dir.x = dx / mx; input.dir.y = dy / mx;
  }
}, { passive: true });
const endJoy = (e) => { for (const t of e.changedTouches) if (input.joy && t.identifier === input.joy.id) { input.joy = null; joy.style.display = 'none'; } };
canvas.addEventListener('touchend', endJoy); canvas.addEventListener('touchcancel', endJoy);
$('btnSplit').addEventListener('pointerdown', (e) => { e.preventDefault(); if (game.state === 'play') split(player); });
let ejectIv = 0;
$('btnEject').addEventListener('pointerdown', (e) => { e.preventDefault(); if (game.state !== 'play') return; eject(player); clearInterval(ejectIv); ejectIv = setInterval(() => game.state === 'play' && eject(player), 120); });
['pointerup', 'pointerleave', 'pointercancel'].forEach((ev) => $('btnEject').addEventListener(ev, () => clearInterval(ejectIv)));

function steerPlayer() {
  if (!player || !player.cells.length) return;
  if (input.mouse) {
    player.tx = cam.x + (input.mx - innerWidth / 2) / cam.s;
    player.ty = cam.y + (input.my - innerHeight / 2) / cam.s;
  } else {
    const c = player.center(), mag = Math.hypot(input.dir.x, input.dir.y);
    const reach = 260 + Math.sqrt(player.mass) * 20;
    if (mag < 0.12) { player.tx = c.x; player.ty = c.y; }
    else { player.tx = c.x + input.dir.x * reach; player.ty = c.y + input.dir.y * reach; }
  }
}

// ───────────────────────── loop ─────────────────────────
let last = performance.now();
function frame(t) {
  const dt = Math.min(0.05, (t - last) / 1000); last = t;
  now += dt;
  if (game.state === 'play' || game.state === 'dead' || game.state === 'menu') {
    steerPlayer();
    step(dt);
  }
  if (game.state === 'menu') { cam.x += Math.cos(now * 0.05) * 30 * dt; cam.y += Math.sin(now * 0.05) * 30 * dt; }
  else updateCamera(dt);
  draw(dt);
  hud(dt);
  requestAnimationFrame(frame);
}

function boot() {
  resize(); addEventListener('resize', resize);
  genWorld(); renderMap();
  STORM = makeStorm(); SPR = makeSprites();
  populate();
  for (let i = 0; i < game.popTarget; i++) addBot(true);
  const s = randomSea(true); cam.x = s.x; cam.y = s.y; cam.s = Math.sqrt(innerWidth * innerHeight) / 1100;
  $('loading').classList.add('hidden');
  try { $('nameIn').value = localStorage.getItem('tempestad-nombre') || ''; } catch { /* sin storage */ }
  $('play').onclick = () => {
    initAudio();
    try { localStorage.setItem('tempestad-nombre', $('nameIn').value.trim()); } catch { /* sin storage */ }
    $('start').classList.add('hidden'); spawnPlayer();
  };
  $('again').onclick = () => spawnPlayer();
  window.__tp = { game, storms, objs, peaks, get player() { return player; }, split, eject };
  requestAnimationFrame(frame);
}
setTimeout(boot, 30);
