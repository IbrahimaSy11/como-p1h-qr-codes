// ==UserScript==
// @name         COMO P-1-H Scannable ID QR Codes
// @namespace    https://github.com/uny2-ops
// @version      1.3.3
// @description  Finds P-1-H Scannable IDs, opens a printable QR grid, and lets you click one QR to scan it alone with left/right navigation
// @author       Ibrahim
// @homepageURL  https://github.com/IbrahimaSy11/como-p1h-qr-codes
// @supportURL   https://github.com/IbrahimaSy11/como-p1h-qr-codes/issues
// @updateURL    https://raw.githubusercontent.com/IbrahimaSy11/como-p1h-qr-codes/main/como-p1h-qr-codes.user.js
// @downloadURL  https://raw.githubusercontent.com/IbrahimaSy11/como-p1h-qr-codes/main/como-p1h-qr-codes.user.js
// @match        https://como-operations-dashboard-iad.iad.proxy.amazon.com/store/*/task/*
// @match        https://como-operations-dashboard-iad.iad.proxy.amazon.com/store/*/jobdetails*
// @match        https://como-operations-dashboard-iad.iad.proxy.amazon.com/store/*/dash*
// @match        https://como-operations-dashboard-iad.iad.proxy.amazon.com/store/*/tasks*
// @match        https://como-operations-dashboard-iad.iad.proxy.amazon.com/store/*/jobs*
// @grant        none
// ==/UserScript==

(function () {
'use strict';

/* ══════════════════════════════════════════════════════════
   CONFIGURATION
══════════════════════════════════════════════════════════ */
var TARGET_PREFIX = 'P-1-H';   // Last Known Location must START WITH this
var ECC_LEVEL     = 'M';       // QR error correction: L < M < Q < H
var MODULE_PX     = 8;         // pixels per QR module (print crispness)
var QUIET_ZONE    = 4;         // quiet-zone modules (spec minimum is 4)

/* Header text used to locate the two columns (matched case-insensitively) */
var COL_LOCATION  = 'last known location';
var COL_SCANNABLE = 'scannable';


/* ══════════════════════════════════════════════════════════
   QR ENCODER  (self-contained: byte mode, versions 1-10)

   No CDN / @require — this dashboard sits behind a corporate
   proxy, so an external library could be blocked and the script
   would silently fail.

   Verified before release: every matrix compared bit-for-bit
   against the `qrcode` reference implementation, and 3000+
   generated codes decoded back with the jsQR decoder (100% pass).
══════════════════════════════════════════════════════════ */
function buildQR(text, eccLevel) {

  /* [blockCount, totalCodewords, dataCodewords] triplets per version/level */
  var RS = {
    1:  { L:[1,26,19],         M:[1,26,16],         Q:[1,26,13],         H:[1,26,9] },
    2:  { L:[1,44,34],         M:[1,44,28],         Q:[1,44,22],         H:[1,44,16] },
    3:  { L:[1,70,55],         M:[1,70,44],         Q:[2,35,17],         H:[2,35,13] },
    4:  { L:[1,100,80],        M:[2,50,32],         Q:[2,50,24],         H:[4,25,9] },
    5:  { L:[1,134,108],       M:[2,67,43],         Q:[2,33,15,2,34,16], H:[2,33,11,2,34,12] },
    6:  { L:[2,86,68],         M:[4,43,27],         Q:[4,43,19],         H:[4,43,15] },
    7:  { L:[2,98,78],         M:[4,49,31],         Q:[2,32,14,4,33,15], H:[4,39,13,1,40,14] },
    8:  { L:[2,121,97],        M:[2,60,38,2,61,39], Q:[4,40,18,2,41,19], H:[4,40,14,2,41,15] },
    9:  { L:[2,146,116],       M:[3,58,36,2,59,37], Q:[4,36,16,4,37,17], H:[4,36,12,4,37,13] },
    10: { L:[2,86,68,2,87,69], M:[4,69,43,1,70,44], Q:[6,43,19,2,44,20], H:[6,43,15,2,44,16] }
  };
  var ALIGN = {
    1:[], 2:[6,18], 3:[6,22], 4:[6,26], 5:[6,30],
    6:[6,34], 7:[6,22,38], 8:[6,24,42], 9:[6,26,46], 10:[6,28,50]
  };
  var ECC_BITS = { L:1, M:0, Q:3, H:2 };

  /* GF(256), primitive polynomial 0x11D */
  var EXP = new Array(512), LOG = new Array(256);
  (function () {
    var x = 1;
    for (var i = 0; i < 255; i++) { EXP[i] = x; LOG[x] = i; x <<= 1; if (x & 0x100) x ^= 0x11D; }
    for (var j = 255; j < 512; j++) EXP[j] = EXP[j - 255];
  })();
  function gmul(a, b) { return (a === 0 || b === 0) ? 0 : EXP[LOG[a] + LOG[b]]; }

  function genPoly(degree) {
    var poly = [1];
    for (var i = 0; i < degree; i++) {
      var next = new Array(poly.length + 1);
      for (var k = 0; k < next.length; k++) next[k] = 0;
      for (var j = 0; j < poly.length; j++) {
        next[j]     ^= poly[j];                 /* multiply by x   */
        next[j + 1] ^= gmul(poly[j], EXP[i]);   /* multiply by a^i */
      }
      poly = next;
    }
    return poly;
  }

  function rsEncode(data, ecCount) {
    var gen = genPoly(ecCount), res = new Array(ecCount);
    for (var i = 0; i < ecCount; i++) res[i] = 0;
    for (var d = 0; d < data.length; d++) {
      var factor = data[d] ^ res[0];
      res.shift(); res.push(0);
      for (var g = 0; g < gen.length - 1; g++) res[g] ^= gmul(gen[g + 1], factor);
    }
    return res;
  }

  function toBytes(str) {
    var out = [];
    for (var i = 0; i < str.length; i++) {
      var c = str.charCodeAt(i);
      if (c < 0x80) out.push(c);
      else if (c < 0x800) out.push(0xC0 | (c >> 6), 0x80 | (c & 0x3F));
      else if (c < 0xD800 || c >= 0xE000) out.push(0xE0 | (c >> 12), 0x80 | ((c >> 6) & 0x3F), 0x80 | (c & 0x3F));
      else {
        i++;
        var cp = 0x10000 + (((c & 0x3FF) << 10) | (str.charCodeAt(i) & 0x3FF));
        out.push(0xF0 | (cp >> 18), 0x80 | ((cp >> 12) & 0x3F), 0x80 | ((cp >> 6) & 0x3F), 0x80 | (cp & 0x3F));
      }
    }
    return out;
  }

  function dataCapacity(ver, ecc) {
    var t = RS[ver][ecc], total = 0;
    for (var i = 0; i < t.length; i += 3) total += t[i] * t[i + 2];
    return total;
  }

  var ecc = ECC_BITS.hasOwnProperty(eccLevel) ? eccLevel : 'M';
  var bytes = toBytes(text);

  var version = 0;
  for (var v = 1; v <= 10; v++) {
    var countBits = (v <= 9) ? 8 : 16;
    if (dataCapacity(v, ecc) * 8 >= 4 + countBits + bytes.length * 8) { version = v; break; }
  }
  if (!version) throw new Error('value too long for QR (' + bytes.length + ' bytes)');

  var size = version * 4 + 17;
  var capacityBits = dataCapacity(version, ecc) * 8;

  var bits = [];
  function put(val, len) { for (var i = len - 1; i >= 0; i--) bits.push((val >>> i) & 1); }

  put(4, 4);                                     /* byte mode */
  put(bytes.length, version <= 9 ? 8 : 16);
  for (var b = 0; b < bytes.length; b++) put(bytes[b], 8);

  var term = Math.min(4, capacityBits - bits.length);
  if (term > 0) put(0, term);
  while (bits.length % 8 !== 0) bits.push(0);

  var dataCw = [];
  for (var i2 = 0; i2 < bits.length; i2 += 8) {
    var bv = 0;
    for (var k2 = 0; k2 < 8; k2++) bv = (bv << 1) | bits[i2 + k2];
    dataCw.push(bv);
  }
  var PAD = [0xEC, 0x11], p = 0;
  while (dataCw.length < capacityBits / 8) { dataCw.push(PAD[p % 2]); p++; }

  var tbl = RS[version][ecc], blocks = [], offset = 0, maxData = 0, maxEc = 0;
  for (var t2 = 0; t2 < tbl.length; t2 += 3) {
    var cnt = tbl[t2], totalCw = tbl[t2 + 1], dCw = tbl[t2 + 2], ecCw = totalCw - dCw;
    for (var c = 0; c < cnt; c++) {
      var dd = dataCw.slice(offset, offset + dCw);
      offset += dCw;
      blocks.push({ data: dd, ec: rsEncode(dd, ecCw) });
      if (dCw > maxData) maxData = dCw;
      if (ecCw > maxEc) maxEc = ecCw;
    }
  }
  var final = [];
  for (var i3 = 0; i3 < maxData; i3++)
    for (var bl = 0; bl < blocks.length; bl++)
      if (i3 < blocks[bl].data.length) final.push(blocks[bl].data[i3]);
  for (var i4 = 0; i4 < maxEc; i4++)
    for (var bl2 = 0; bl2 < blocks.length; bl2++)
      if (i4 < blocks[bl2].ec.length) final.push(blocks[bl2].ec[i4]);

  function blank() {
    var m = new Array(size);
    for (var r = 0; r < size; r++) { m[r] = new Array(size); for (var cc = 0; cc < size; cc++) m[r][cc] = null; }
    return m;
  }
  function placeFinder(m, row, col) {
    for (var r = -1; r <= 7; r++) for (var cx = -1; cx <= 7; cx++) {
      var rr = row + r, cc = col + cx;
      if (rr < 0 || rr >= size || cc < 0 || cc >= size) continue;
      m[rr][cc] = (r >= 0 && r <= 6 && (cx === 0 || cx === 6)) ||
                  (cx >= 0 && cx <= 6 && (r === 0 || r === 6)) ||
                  (r >= 2 && r <= 4 && cx >= 2 && cx <= 4);
    }
  }
  function placeAlign(m) {
    var pos = ALIGN[version];
    for (var i5 = 0; i5 < pos.length; i5++) for (var j5 = 0; j5 < pos.length; j5++) {
      var row = pos[i5], col = pos[j5];
      if (m[row][col] !== null) continue;
      for (var r = -2; r <= 2; r++) for (var cx = -2; cx <= 2; cx++)
        m[row + r][col + cx] = (Math.max(Math.abs(r), Math.abs(cx)) !== 1);
    }
  }
  function reserveFormat(m) {
    for (var i6 = 0; i6 < 9; i6++) {
      if (m[8][i6] === null) m[8][i6] = false;
      if (m[i6][8] === null) m[i6][8] = false;
    }
    for (var j6 = 0; j6 < 8; j6++) {
      if (m[8][size - 1 - j6] === null) m[8][size - 1 - j6] = false;
      if (m[size - 1 - j6][8] === null) m[size - 1 - j6][8] = false;
    }
  }

  var matrix = blank();
  placeFinder(matrix, 0, 0);
  placeFinder(matrix, 0, size - 7);
  placeFinder(matrix, size - 7, 0);
  placeAlign(matrix);
  for (var i7 = 8; i7 < size - 8; i7++) {
    if (matrix[6][i7] === null) matrix[6][i7] = (i7 % 2 === 0);
    if (matrix[i7][6] === null) matrix[i7][6] = (i7 % 2 === 0);
  }
  matrix[size - 8][8] = true;
  reserveFormat(matrix);
  if (version >= 7) {
    for (var a = 0; a < 6; a++) for (var b2 = 0; b2 < 3; b2++) {
      matrix[size - 11 + b2][a] = false;
      matrix[a][size - 11 + b2] = false;
    }
  }

  var reserved = new Array(size);
  for (var r2 = 0; r2 < size; r2++) {
    reserved[r2] = new Array(size);
    for (var c5 = 0; c5 < size; c5++) reserved[r2][c5] = (matrix[r2][c5] !== null);
  }

  (function placeData(m) {
    var bitIdx = 0, upward = true;
    for (var col = size - 1; col > 0; col -= 2) {
      if (col === 6) col--;
      for (var n = 0; n < size; n++) {
        var row = upward ? (size - 1 - n) : n;
        for (var s = 0; s < 2; s++) {
          var cc = col - s;
          if (reserved[row][cc]) continue;
          var bit = false;
          if (bitIdx < final.length * 8) bit = ((final[bitIdx >> 3] >>> (7 - (bitIdx & 7))) & 1) === 1;
          m[row][cc] = bit;
          bitIdx++;
        }
      }
      upward = !upward;
    }
  })(matrix);

  function maskFn(id, r, c) {
    switch (id) {
      case 0: return (r + c) % 2 === 0;
      case 1: return r % 2 === 0;
      case 2: return c % 3 === 0;
      case 3: return (r + c) % 3 === 0;
      case 4: return (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0;
      case 5: return ((r * c) % 2) + ((r * c) % 3) === 0;
      case 6: return (((r * c) % 2) + ((r * c) % 3)) % 2 === 0;
      case 7: return (((r + c) % 2) + ((r * c) % 3)) % 2 === 0;
    }
    return false;
  }
  function formatBits(eccB, maskId) {
    var data = (eccB << 3) | maskId, rem = data << 10;
    for (var i8 = 14; i8 >= 10; i8--) if ((rem >>> i8) & 1) rem ^= 0x537 << (i8 - 10);
    return ((data << 10) | rem) ^ 0x5412;
  }
  function versionBits(ver) {
    var rem = ver << 12;
    for (var i9 = 17; i9 >= 12; i9--) if ((rem >>> i9) & 1) rem ^= 0x1F25 << (i9 - 12);
    return (ver << 12) | rem;
  }
  function applyFormat(m, maskId) {
    var f = formatBits(ECC_BITS[ecc], maskId);
    for (var i10 = 0; i10 < 15; i10++) {
      var on10 = ((f >>> i10) & 1) === 1;
      if (i10 < 6)      m[i10][8] = on10;
      else if (i10 < 8) m[i10 + 1][8] = on10;
      else              m[size - 15 + i10][8] = on10;
    }
    for (var i11 = 0; i11 < 15; i11++) {
      var on11 = ((f >>> i11) & 1) === 1;
      if (i11 < 8)      m[8][size - i11 - 1] = on11;
      else if (i11 < 9) m[8][15 - i11 - 1 + 1] = on11;
      else              m[8][15 - i11 - 1] = on11;
    }
    m[size - 8][8] = true;
    if (version >= 7) {
      var vb = versionBits(version);
      for (var i14 = 0; i14 < 18; i14++) {
        var on = ((vb >>> i14) & 1) === 1;
        m[Math.floor(i14 / 3)][size - 11 + (i14 % 3)] = on;
        m[size - 11 + (i14 % 3)][Math.floor(i14 / 3)] = on;
      }
    }
  }

  function penalty(m) {
    var score = 0, r, c, run;
    for (r = 0; r < size; r++) {
      run = 1;
      for (c = 1; c < size; c++) {
        if (m[r][c] === m[r][c - 1]) run++;
        else { if (run >= 5) score += 3 + (run - 5); run = 1; }
      }
      if (run >= 5) score += 3 + (run - 5);
    }
    for (c = 0; c < size; c++) {
      run = 1;
      for (r = 1; r < size; r++) {
        if (m[r][c] === m[r - 1][c]) run++;
        else { if (run >= 5) score += 3 + (run - 5); run = 1; }
      }
      if (run >= 5) score += 3 + (run - 5);
    }
    for (r = 0; r < size - 1; r++) for (c = 0; c < size - 1; c++) {
      var v2 = m[r][c];
      if (v2 === m[r][c + 1] && v2 === m[r + 1][c] && v2 === m[r + 1][c + 1]) score += 3;
    }
    var pat1 = [true,false,true,true,true,false,true,false,false,false,false];
    var pat2 = [false,false,false,false,true,false,true,true,true,false,true];
    function matches(get, start) {
      var okA = true, okB = true;
      for (var k = 0; k < 11; k++) {
        var val = get(start + k);
        if (val !== pat1[k]) okA = false;
        if (val !== pat2[k]) okB = false;
      }
      return okA || okB;
    }
    for (r = 0; r < size; r++) for (c = 0; c <= size - 11; c++) {
      (function (rr, cc) { if (matches(function (x) { return m[rr][x]; }, cc)) score += 40; })(r, c);
    }
    for (c = 0; c < size; c++) for (r = 0; r <= size - 11; r++) {
      (function (rr, cc) { if (matches(function (x) { return m[x][cc]; }, rr)) score += 40; })(r, c);
    }
    var dark = 0;
    for (r = 0; r < size; r++) for (c = 0; c < size; c++) if (m[r][c]) dark++;
    score += Math.floor(Math.abs((dark * 100 / (size * size)) - 50) / 5) * 10;
    return score;
  }

  var best = null, bestScore = Infinity;
  for (var mk = 0; mk < 8; mk++) {
    var cand = new Array(size);
    for (var r3 = 0; r3 < size; r3++) {
      cand[r3] = new Array(size);
      for (var c6 = 0; c6 < size; c6++) {
        var val3 = matrix[r3][c6];
        if (!reserved[r3][c6] && maskFn(mk, r3, c6)) val3 = !val3;
        cand[r3][c6] = val3;
      }
    }
    applyFormat(cand, mk);
    var sc = penalty(cand);
    if (sc < bestScore) { bestScore = sc; best = cand; }
  }
  return { matrix: best, size: size, version: version };
}

/* Render a value to a PNG data URL */
function qrDataURL(value) {
  var qr = buildQR(value, ECC_LEVEL);
  var dim = (qr.size + QUIET_ZONE * 2) * MODULE_PX;
  var cv = document.createElement('canvas');
  cv.width = dim; cv.height = dim;
  var g = cv.getContext('2d');
  g.fillStyle = '#ffffff'; g.fillRect(0, 0, dim, dim);
  g.fillStyle = '#000000';
  for (var r = 0; r < qr.size; r++) {
    for (var c = 0; c < qr.size; c++) {
      if (qr.matrix[r][c]) {
        g.fillRect((c + QUIET_ZONE) * MODULE_PX, (r + QUIET_ZONE) * MODULE_PX, MODULE_PX, MODULE_PX);
      }
    }
  }
  return cv.toDataURL('image/png');
}


/* ══════════════════════════════════════════════════════════
   TABLE SCRAPING
══════════════════════════════════════════════════════════ */
function norm(s) {
  return (s || '').replace(/\s+/g, ' ').trim().toLowerCase();
}

/* Locate the table plus the two column indices we need. */
function findTable() {
  var tables = document.querySelectorAll('table');
  for (var t = 0; t < tables.length; t++) {
    var table = tables[t];

    /* header cells: prefer <th>, else the first row's cells */
    var heads = table.querySelectorAll('thead th, thead td');
    if (!heads.length) heads = table.querySelectorAll('th');
    if (!heads.length) {
      var firstRow = table.querySelector('tr');
      if (firstRow) heads = firstRow.querySelectorAll('td, th');
    }
    if (!heads.length) continue;

    var locIdx = -1, idIdx = -1;
    for (var h = 0; h < heads.length; h++) {
      var txt = norm(heads[h].textContent);
      if (locIdx === -1 && txt.indexOf(COL_LOCATION) !== -1) locIdx = h;
      if (idIdx === -1 && txt.indexOf(COL_SCANNABLE) !== -1) idIdx = h;
    }
    if (locIdx !== -1 && idIdx !== -1) {
      return { table: table, locIdx: locIdx, idIdx: idIdx, headerCount: heads.length };
    }
  }
  return null;
}

/* Returns { items:[{location, scannableId}], total, error } */
function scrapeRows() {
  var found = findTable();
  if (!found) {
    return { items: [], total: 0, error:
      'Could not find a table containing both a "Last Known Location" and a "Scannable ID" column on this page.' };
  }

  var rows = found.table.querySelectorAll('tbody tr');
  if (!rows.length) rows = found.table.querySelectorAll('tr');

  var seen = {}, items = [], total = 0;

  for (var i = 0; i < rows.length; i++) {
    var cells = rows[i].querySelectorAll('td');
    if (!cells.length) continue;                                  /* header row */
    if (cells.length <= Math.max(found.locIdx, found.idIdx)) continue;

    var locRaw = (cells[found.locIdx].textContent || '').replace(/\s+/g, ' ').trim();
    var idRaw  = (cells[found.idIdx].textContent  || '').replace(/\s+/g, ' ').trim();
    if (!locRaw || !idRaw) continue;

    total++;

    /* Location must BEGIN WITH the target prefix */
    if (locRaw.toUpperCase().indexOf(TARGET_PREFIX.toUpperCase()) !== 0) continue;

    /* de-duplicate on the location + scannable ID pair */
    var key = locRaw.toUpperCase() + '\u0000' + idRaw.toUpperCase();
    if (seen[key]) continue;
    seen[key] = true;

    items.push({ location: locRaw, scannableId: idRaw });
  }

  return { items: items, total: total, error: null };
}


/* ══════════════════════════════════════════════════════════
   OUTPUT TAB
══════════════════════════════════════════════════════════ */
function esc(s) {
  return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;')
                  .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

function buildTabHTML(items) {
  var cards = '', failed = [];

  for (var i = 0; i < items.length; i++) {
    var it = items[i], url;
    try {
      url = qrDataURL(it.scannableId);
    } catch (e) {
      failed.push(it.location + ' (' + e.message + ')');
      continue;
    }
    cards +=
      '<div class="card" data-index="' + i + '">' +
        '<img class="qr-img" src="' + url + '" alt="QR for ' + esc(it.scannableId) + '" ' +
          'title="Click to open this QR by itself">' +
        '<div class="loc">' + esc(it.location) + '</div>' +
        '<div class="sid">' + esc(it.scannableId) + '</div>' +
      '</div>';
  }

  var warn = failed.length
    ? '<div class="warn">Skipped ' + failed.length + ': ' + esc(failed.join(', ')) + '</div>'
    : '';
  var stamp = new Date().toLocaleString();

  return (
'<!DOCTYPE html><html><head><meta charset="utf-8">' +
'<title>' + esc(TARGET_PREFIX) + ' QR Codes (' + items.length + ')</title>' +
'<style>' +
'*{box-sizing:border-box}' +
'body{margin:0;padding:20px 24px 32px;background:#fff;color:#111;' +
  'font-family:-apple-system,"Segoe UI","Helvetica Neue",Arial,sans-serif}' +
'header{display:flex;align-items:center;justify-content:space-between;gap:16px;' +
  'padding-bottom:14px;border-bottom:2px solid #111;margin-bottom:20px}' +
'h1{margin:0;font-size:19px;letter-spacing:.02em}' +
'.meta{font-size:12px;color:#666;margin-top:3px}' +
'button{font:inherit;font-size:14px;font-weight:700;padding:9px 18px;cursor:pointer;' +
  'background:#111;color:#fff;border:none;border-radius:7px}' +
'button:hover{background:#333}' +
'.warn{background:#fff3cd;border:1px solid #ffc107;border-radius:7px;padding:9px 12px;' +
  'font-size:13px;color:#856404;margin-bottom:16px}' +
'.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(215px,1fr));gap:18px}' +
'.card{border:1px solid #ccc;border-radius:9px;padding:12px 10px 10px;text-align:center;' +
  'background:#fff;break-inside:avoid;page-break-inside:avoid}' +
'.card img{width:100%;max-width:190px;height:auto;display:block;margin:0 auto 9px;' +
  'image-rendering:pixelated;image-rendering:crisp-edges}' +
'.loc{font-size:16px;font-weight:800;letter-spacing:.02em;word-break:break-all;line-height:1.25}' +
'.sid{font-family:"SF Mono",Consolas,monospace;font-size:10.5px;color:#666;' +
  'margin-top:4px;word-break:break-all}' +
'.qr-img{cursor:zoom-in;border-radius:4px;transition:transform .15s ease,box-shadow .15s ease}' +
'.qr-img:hover{transform:scale(1.025);box-shadow:0 4px 14px rgba(0,0,0,.14)}' +
'.viewer{position:fixed;inset:0;z-index:999999;background:rgba(0,0,0,.82);' +
  'display:none;align-items:center;justify-content:center;padding:24px}' +
'.viewer.open{display:flex}' +
'.viewer-box{position:relative;width:min(86vw,600px);max-height:90vh;background:#fff;color:#111;' +
  'border-radius:14px;padding:22px 76px 20px;text-align:center;box-shadow:0 18px 60px rgba(0,0,0,.45);' +
  'display:flex;flex-direction:column;align-items:center;justify-content:center}' +
'.viewer-qr{display:block;width:min(52vh,420px);height:auto;max-width:100%;' +
  'image-rendering:pixelated;image-rendering:crisp-edges;background:#fff}' +
'.viewer-loc{margin-top:12px;font-size:22px;font-weight:900;line-height:1.2;word-break:break-all}' +
'.viewer-sid{margin-top:5px;font-family:"SF Mono",Consolas,monospace;font-size:13px;color:#555;word-break:break-all}' +
'.viewer-count{margin-top:8px;font-size:12px;font-weight:700;color:#777}' +
'.viewer-close{position:absolute;top:10px;right:12px;width:40px;height:40px;padding:0;' +
  'border-radius:50%;background:#111;color:#fff;font-size:24px;line-height:40px}' +
'.viewer-close:hover{background:#333}' +
'.viewer-nav{position:absolute;top:50%;transform:translateY(-50%);width:50px;height:72px;' +
  'padding:0;border-radius:10px;background:#111;color:#fff;font-size:34px;line-height:1}' +
'.viewer-prev{left:12px}.viewer-next{right:12px}' +
'.viewer-help{position:absolute;left:50%;bottom:14px;transform:translateX(-50%);' +
  'color:#fff;font-size:12px;font-weight:700;opacity:.85;white-space:nowrap}' +
'@media(max-width:560px){.viewer{padding:10px}.viewer-box{padding:52px 56px 18px}.viewer-nav{width:42px;height:60px}.viewer-prev{left:7px}.viewer-next{right:7px}.viewer-loc{font-size:18px}}' +
'@media print{' +
  'body{padding:0}' +
  '.no-print,.viewer{display:none !important}' +
  'header{border-bottom:1px solid #000;margin-bottom:12px;padding-bottom:8px}' +
  '.grid{grid-template-columns:repeat(3,1fr);gap:12px}' +
  '.card{border:1px solid #999}' +
  '@page{margin:12mm}' +
'}' +
'</style></head><body>' +
'<header>' +
  '<div><h1>' + esc(TARGET_PREFIX) + ' &mdash; ' + items.length + ' QR code' + (items.length === 1 ? '' : 's') + '</h1>' +
  '<div class="meta">QR value = Scannable ID &middot; click any QR to scan it alone &middot; generated ' + esc(stamp) + '</div></div>' +
  '<button class="no-print" onclick="window.print()">Print</button>' +
'</header>' +
warn +
'<div class="grid">' + cards + '</div>' +
'<div id="qr-viewer" class="viewer no-print" aria-hidden="true">' +
  '<div class="viewer-box" role="dialog" aria-modal="true" aria-label="Single QR code viewer">' +
    '<button id="viewer-close" class="viewer-close" type="button" title="Close">&times;</button>' +
    '<button id="viewer-prev" class="viewer-nav viewer-prev" type="button" title="Previous QR">&#8249;</button>' +
    '<img id="viewer-qr" class="viewer-qr" alt="Selected QR code">' +
    '<div id="viewer-loc" class="viewer-loc"></div>' +
    '<div id="viewer-sid" class="viewer-sid"></div>' +
    '<div id="viewer-count" class="viewer-count"></div>' +
    '<button id="viewer-next" class="viewer-nav viewer-next" type="button" title="Next QR">&#8250;</button>' +
  '</div>' +
  '<div class="viewer-help">Left / Right arrows = next QR &nbsp;&middot;&nbsp; Esc = close</div>' +
'</div>' +
'<script>' +
'(function(){' +
  'var cards=Array.prototype.slice.call(document.querySelectorAll(".card"));' +
  'var viewer=document.getElementById("qr-viewer");' +
  'var box=viewer.querySelector(".viewer-box");' +
  'var qr=document.getElementById("viewer-qr");' +
  'var loc=document.getElementById("viewer-loc");' +
  'var sid=document.getElementById("viewer-sid");' +
  'var count=document.getElementById("viewer-count");' +
  'var current=0;' +
  'function show(i){' +
    'if(!cards.length)return;' +
    'current=(i+cards.length)%cards.length;' +
    'var card=cards[current];' +
    'var img=card.querySelector(".qr-img");' +
    'qr.src=img.src;' +
    'qr.alt=img.alt;' +
    'loc.textContent=card.querySelector(".loc").textContent;' +
    'sid.textContent=card.querySelector(".sid").textContent;' +
    'count.textContent=(current+1)+" / "+cards.length;' +
  '}' +
  'function openAt(i){show(i);viewer.classList.add("open");viewer.setAttribute("aria-hidden","false");document.body.style.overflow="hidden";document.getElementById("viewer-close").focus();}' +
  'function closeViewer(){viewer.classList.remove("open");viewer.setAttribute("aria-hidden","true");document.body.style.overflow="";}' +
  'cards.forEach(function(card,i){var img=card.querySelector(".qr-img");img.addEventListener("click",function(){openAt(i);});});' +
  'document.getElementById("viewer-prev").addEventListener("click",function(){show(current-1);});' +
  'document.getElementById("viewer-next").addEventListener("click",function(){show(current+1);});' +
  'document.getElementById("viewer-close").addEventListener("click",closeViewer);' +
  'viewer.addEventListener("click",function(e){if(e.target===viewer)closeViewer();});' +
  'box.addEventListener("click",function(e){e.stopPropagation();});' +
  'document.addEventListener("keydown",function(e){' +
    'if(!viewer.classList.contains("open"))return;' +
    'if(e.key==="ArrowLeft"){e.preventDefault();show(current-1);}' +
    'else if(e.key==="ArrowRight"){e.preventDefault();show(current+1);}' +
    'else if(e.key==="Escape"){e.preventDefault();closeViewer();}' +
  '});' +
  'if(cards.length){setTimeout(function(){openAt(0);},0);}' +
'})();' +
'<\/script>' +
'</body></html>'
  );
}

/* Write HTML to a tab; returns true on success, false if the write was blocked. */
function writeToTab(win, html) {
  try {
    win.document.open();
    win.document.write(html);
    win.document.close();
    /* Verify something actually landed — a blocked/sandboxed write leaves
       the document empty or in a default state. */
    return !!(win.document.body && win.document.body.innerHTML.length > 100);
  } catch (e) {
    return false;
  }
}

function openQRTab(items, win) {
  var html = buildTabHTML(items);
  if (writeToTab(win, html)) return true;

  /* Write failed (some browsers block document.write on cross-origin blobs).
     Fall back to a Blob URL — no cross-origin restriction. */
  try {
    var blob = new Blob([html], { type: 'text/html' });
    var url  = URL.createObjectURL(blob);
    win.location.href = url;
    /* Revoke after a generous delay so the page finishes loading. */
    setTimeout(function () { try { URL.revokeObjectURL(url); } catch (e2) {} }, 60000);
    return true;
  } catch (e) {
    return false;
  }
}


/* ══════════════════════════════════════════════════════════
   UI — button + toast
══════════════════════════════════════════════════════════ */
var style = document.createElement('style');
style.textContent =
  '#p1hqr-btn{position:fixed;bottom:24px;left:24px;z-index:99999;background:#0d6efd;color:#fff;' +
    'border:none;border-radius:60px;padding:24px 46px;font-size:28px;font-weight:800;' +
    'letter-spacing:.02em;line-height:1.1;' +
    'font-family:"Segoe UI",system-ui,sans-serif;box-shadow:0 6px 20px rgba(13,110,253,.45);' +
    'cursor:pointer;transition:transform .2s,box-shadow .2s;user-select:none;display:none}' +
  '#p1hqr-btn:hover{transform:scale(1.04);box-shadow:0 9px 26px rgba(13,110,253,.55)}' +
  '#p1hqr-btn:active{transform:scale(.98)}' +
  '#p1hqr-btn.visible{display:block}' +
  '#p1hqr-btn.busy{background:#6c757d;box-shadow:0 4px 14px rgba(108,117,125,.42)}' +
  '#p1hqr-toast{position:fixed;bottom:130px;left:24px;z-index:99999;max-width:400px;' +
    'background:#111;color:#fff;font:14px/1.45 "Segoe UI",system-ui,sans-serif;' +
    'padding:13px 17px;border-radius:10px;box-shadow:0 6px 22px rgba(0,0,0,.3);' +
    'opacity:0;transform:translateY(6px);transition:opacity .2s,transform .2s;pointer-events:none}' +
  '#p1hqr-toast.show{opacity:1;transform:none}' +
  '#p1hqr-toast.err{background:#b3261e}';
document.head.appendChild(style);

var btn = document.createElement('button');
btn.id = 'p1hqr-btn';
btn.textContent = '\u2318 QR: ' + TARGET_PREFIX;
btn.title = 'Generate QR codes from Scannable IDs of rows in ' + TARGET_PREFIX;
document.body.appendChild(btn);

var toastEl = document.createElement('div');
toastEl.id = 'p1hqr-toast';
document.body.appendChild(toastEl);

var toastTimer = null;
function toast(msg, isErr) {
  toastEl.textContent = msg;
  toastEl.className = 'show' + (isErr ? ' err' : '');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(function () { toastEl.className = ''; }, isErr ? 7000 : 3500);
}

/* draggable, without swallowing the click */
var dragging = false, offX = 0, offY = 0;
btn.addEventListener('mousedown', function (e) {
  dragging = false;
  var r = btn.getBoundingClientRect();
  offX = e.clientX - r.left; offY = e.clientY - r.top;
  function move(ev) {
    dragging = true;
    btn.style.left = (ev.clientX - offX) + 'px';
    btn.style.top  = (ev.clientY - offY) + 'px';
    btn.style.bottom = 'auto'; btn.style.right = 'auto';
  }
  function up() {
    document.removeEventListener('mousemove', move);
    document.removeEventListener('mouseup', up);
  }
  document.addEventListener('mousemove', move);
  document.addEventListener('mouseup', up);
});

/* Maximum automatic retries if the new tab comes up blank. */
var MAX_RETRIES = 3, RETRY_MS = 900;

/* Every QR-generation click gets its own session id. Navigating away
   invalidates that id, so delayed retries/errors from the previous cart
   cannot appear later on the main dashboard. */
var generationSession = 0;

function generationStillCurrent(sessionId) {
  return sessionId === generationSession;
}

function doGenerate(attempt, sessionId) {
  if (attempt === undefined) attempt = 0;
  if (sessionId === undefined) sessionId = generationSession;
  if (!generationStillCurrent(sessionId)) return;

  var res = scrapeRows();

  if (!generationStillCurrent(sessionId)) return;

  if (res.error) {
    if (!generationStillCurrent(sessionId)) return;
    toast(res.error, true); resetBtn(); return;
  }
  if (!res.items.length) {
    /* Table may not have loaded yet — retry silently a few times
       before giving up with a message. */
    if (attempt < MAX_RETRIES) {
      setTimeout(function () {
        if (generationStillCurrent(sessionId)) doGenerate(attempt + 1, sessionId);
      }, RETRY_MS);
      return;
    }
    if (!generationStillCurrent(sessionId)) return;
    toast('No ' + TARGET_PREFIX + ' rows found after ' + (attempt + 1) + ' attempts ' +
          '(scanned ' + res.total + ' row' + (res.total === 1 ? '' : 's') + ').', true);
    resetBtn();
    return;
  }

  /* Open the tab synchronously (inside a user gesture) to beat popup blockers.
     If it fails, wait and try once more — some browsers allow it on retry. */
  var win = window.open('', '_blank');
  if (!win) {
    if (attempt < 1) {
      if (!generationStillCurrent(sessionId)) return;
      toast('Opening tab — if nothing appears, click again.', false);
      setTimeout(function () {
        if (generationStillCurrent(sessionId)) doGenerate(attempt + 1, sessionId);
      }, 800);
      return;
    }
    if (!generationStillCurrent(sessionId)) return;
    toast('Popup blocked — allow popups for this site in the address bar, then click again.', true);
    resetBtn();
    return;
  }

  setTimeout(function () {
    if (!generationStillCurrent(sessionId)) {
      try { win.close(); } catch (e0) {}
      return;
    }
    var ok = false;
    try {
      ok = openQRTab(res.items, win);
    } catch (e) {
      ok = false;
    }

    if (ok) {
      if (!generationStillCurrent(sessionId)) return;
      toast(res.items.length + ' QR code' + (res.items.length === 1 ? '' : 's') +
            ' opened in a new tab.', false);
      resetBtn();
      return;
    }

    /* Tab opened but write failed — close it, wait, retry. */
    try { win.close(); } catch (e2) {}

    if (!generationStillCurrent(sessionId)) return;
    if (attempt < MAX_RETRIES) {
      toast('Tab loaded blank — retrying (' + (attempt + 1) + '/' + MAX_RETRIES + ')\u2026', false);
      setTimeout(function () {
        if (generationStillCurrent(sessionId)) doGenerate(attempt + 1, sessionId);
      }, RETRY_MS);
    } else {
      toast('Could not write to the new tab after ' + (attempt + 1) + ' tries. ' +
            'Try disabling any extensions that block scripts on new tabs.', true);
      resetBtn();
    }
  }, 0);
}

function resetBtn() {
  btn.classList.remove('busy');
  btn.textContent = '\u2318 QR: ' + TARGET_PREFIX;
}

btn.addEventListener('click', function () {
  if (dragging) { dragging = false; return; }
  generationSession++;
  var thisSession = generationSession;
  btn.classList.add('busy');
  btn.textContent = '\u23F3 building\u2026';
  doGenerate(0, thisSession);
});

/* ══════════════════════════════════════════════════════════
   VISIBILITY — button shows only on a cart/task detail page.

   Hiding is eager (instant), showing is conservative. The
   dashboard mutates constantly, so this uses a leading-edge
   throttle rather than a debounce: a debounce would keep
   getting reset by the stream of mutations and the button
   could linger after navigating away.
══════════════════════════════════════════════════════════ */
var btnVisible = false;
function setVisible(v) {
  if (v === btnVisible) return;
  btnVisible = v;
  if (v) btn.classList.add('visible');
  else   btn.classList.remove('visible');
}

/* Cheap checks — safe to run on every signal.
   true = definitely detail page, false = not obviously one. */
function cheapDetail() {
  if (/\/task\/|jobdetails/i.test(location.href)) return true;
  if (document.querySelector('div.job-details')) return true;
  return false;
}

/* Expensive fallback for non-standard markup — throttled + cached. */
var tblAt = 0, tblRes = false;
function tableDetail() {
  var now = Date.now();
  if (now - tblAt > 600) { tblAt = now; tblRes = !!findTable(); }
  return tblRes;
}

function updateVisibility() {
  if (cheapDetail()) { setVisible(true); return; }
  setVisible(tableDetail());
}

/* On navigation: hide instantly, drop the cache, then re-evaluate. */
function onNavigate() {
  generationSession++;             /* cancel retries/errors from the page we just left */
  setVisible(false);
  tblAt = 0; tblRes = false;
  clearTimeout(toastTimer);
  toastEl.className = '';          /* don't leave a stale message behind */
  resetBtn();
  updateVisibility();
}

/* AngularJS routes via pushState, which does NOT fire popstate —
   patch both history methods so SPA navigation is caught immediately. */
(function () {
  var _push = history.pushState, _replace = history.replaceState;
  history.pushState = function () {
    var r = _push.apply(this, arguments);
    onNavigate();
    return r;
  };
  history.replaceState = function () {
    var r = _replace.apply(this, arguments);
    onNavigate();
    return r;
  };
})();

window.addEventListener('popstate', onNavigate);
window.addEventListener('hashchange', onNavigate);

/* Safety net: catch any URL change the patch above misses. */
var lastHref = location.href;
setInterval(function () {
  if (location.href !== lastHref) { lastHref = location.href; onNavigate(); }
}, 120);

/* Leading-edge throttle — always fires, at most every 150ms.
   Catches in-place removal of the detail view (no URL change). */
var mutAt = 0;
new MutationObserver(function () {
  var now = Date.now();
  if (now - mutAt < 150) return;
  mutAt = now;
  updateVisibility();
}).observe(document.body, { childList: true, subtree: true });

updateVisibility();

console.log('[P1H-QR] v1.3.3 loaded — QR value = Scannable ID, prefix filter = ' + TARGET_PREFIX);

})();
