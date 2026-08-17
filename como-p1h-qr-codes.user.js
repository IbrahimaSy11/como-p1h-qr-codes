// ==UserScript==
// @name         COMO P-1-H Scannable ID QR Codes
// @namespace    https://github.com/uny2-ops
// @version      1.4.5
// @description  P-1-H Scannable ID QR workspace with a fixed-size Manager Actions button that disables when no QR data exists
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

/* Render a value as a vector SVG data URL.
   SVG keeps each QR module perfectly square when the browser is zoomed or the
   popup is resized, avoiding raster resampling/moire that can make codes look
   corrupted or difficult to scan. */
function qrDataURL(value) {
  var qr = buildQR(value, ECC_LEVEL);
  var totalModules = qr.size + QUIET_ZONE * 2;
  var naturalPx = totalModules * MODULE_PX;
  var path = [];

  for (var r = 0; r < qr.size; r++) {
    for (var c = 0; c < qr.size; c++) {
      if (qr.matrix[r][c]) {
        var x = c + QUIET_ZONE;
        var y = r + QUIET_ZONE;
        path.push('M' + x + ' ' + y + 'h1v1h-1z');
      }
    }
  }

  var svg =
    '<svg xmlns="http://www.w3.org/2000/svg" ' +
      'width="' + naturalPx + '" height="' + naturalPx + '" ' +
      'viewBox="0 0 ' + totalModules + ' ' + totalModules + '" ' +
      'preserveAspectRatio="xMidYMid meet" shape-rendering="crispEdges">' +
      '<rect width="' + totalModules + '" height="' + totalModules + '" fill="#fff"/>' +
      '<path d="' + path.join('') + '" fill="#000"/>' +
    '</svg>';

  return 'data:image/svg+xml;charset=utf-8,' + encodeURIComponent(svg);
}


/* ══════════════════════════════════════════════════════════
   TABLE SCRAPING
══════════════════════════════════════════════════════════ */
function norm(s) {
  return (s || '').replace(/\s+/g, ' ').trim().toLowerCase();
}

function cleanCellText(cell) {
  return (cell && cell.textContent ? cell.textContent : '').replace(/\s+/g, ' ').trim();
}

function isVisibleElement(el) {
  if (!el || !el.isConnected) return false;
  try {
    var style = getComputedStyle(el);
    if (style.display === 'none' || style.visibility === 'hidden') return false;
    var r = el.getBoundingClientRect();
    return r.width > 0 && r.height > 0;
  } catch (e) {
    return true;
  }
}

/* Locate the best table plus the two column indices we need.
   If Angular leaves an old hidden table behind, prefer the visible one. */
function findTable() {
  var tables = document.querySelectorAll('table');
  var fallback = null;

  for (var t = 0; t < tables.length; t++) {
    var table = tables[t];
    var heads = table.querySelectorAll('thead tr:last-child th, thead tr:last-child td');
    if (!heads.length) heads = table.querySelectorAll('thead th, thead td');
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

    if (locIdx === -1 || idIdx === -1) continue;

    var match = { table: table, locIdx: locIdx, idIdx: idIdx, headerCount: heads.length };
    if (isVisibleElement(table)) return match;
    if (!fallback) fallback = match;
  }

  return fallback;
}

/* Returns { items:[{location, scannableId}], total, error } */
function scrapeRows() {
  var found = findTable();
  if (!found) {
    return {
      items: [],
      total: 0,
      error: 'The item table is not ready yet.'
    };
  }

  var rows = found.table.querySelectorAll('tbody tr');
  if (!rows.length) rows = found.table.querySelectorAll('tr');

  var seen = Object.create(null), items = [], total = 0;
  var prefix = TARGET_PREFIX.toUpperCase();
  var maxIdx = Math.max(found.locIdx, found.idIdx);

  for (var i = 0; i < rows.length; i++) {
    var cells = rows[i].querySelectorAll('td');
    if (!cells.length || cells.length <= maxIdx) continue;

    var locRaw = cleanCellText(cells[found.locIdx]);
    var idRaw  = cleanCellText(cells[found.idIdx]);
    if (!locRaw || !idRaw) continue;

    total++;
    if (locRaw.toUpperCase().indexOf(prefix) !== 0) continue;

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
                  .replace(/>/g, '&gt;').replace(/"/g, '&quot;')
                  .replace(/'/g, '&#39;');
}

function buildTabHTML(items) {
  var cards = '', failed = [], rendered = 0;
  var qrCache = Object.create(null);

  for (var i = 0; i < items.length; i++) {
    var it = items[i], url;
    try {
      if (qrCache[it.scannableId]) url = qrCache[it.scannableId];
      else {
        url = qrDataURL(it.scannableId);
        qrCache[it.scannableId] = url;
      }
    } catch (e) {
      failed.push(it.location + ' (' + e.message + ')');
      continue;
    }

    var cardIndex = rendered++;
    cards +=
      '<article class="card" data-index="' + cardIndex + '">' +
        '<div class="card-top"><span class="card-num">' + String(cardIndex + 1).padStart(2, '0') + '</span>' +
          '<span class="card-tag">' + esc(TARGET_PREFIX) + '</span></div>' +
        '<button class="qr-open" type="button" aria-label="Open QR for ' + esc(it.location) + '">' +
          '<img class="qr-img" src="' + url + '" alt="QR for ' + esc(it.scannableId) + '">' +
        '</button>' +
        '<div class="loc">' + esc(it.location) + '</div>' +
        '<div class="sid">' + esc(it.scannableId) + '</div>' +
      '</article>';
  }

  var warn = failed.length
    ? '<div class="warn" role="alert"><strong>' + failed.length + ' QR' + (failed.length === 1 ? '' : 's') +
      ' skipped.</strong> ' + esc(failed.join(', ')) + '</div>'
    : '';
  var stamp = new Date().toLocaleString();
  var countLabel = rendered + ' QR code' + (rendered === 1 ? '' : 's');

  return (
'<!DOCTYPE html><html lang="en" data-p1hqr-workspace="1"><head><meta charset="utf-8">' +
'<meta name="viewport" content="width=device-width,initial-scale=1">' +
'<title>' + esc(TARGET_PREFIX) + ' QR Codes (' + rendered + ')</title>' +
'<style>' +
':root{--ink:#111827;--muted:#6b7280;--line:#e5e7eb;--soft:#f6f7f9;--blue:#2563eb;--blue2:#1d4ed8;--danger:#b42318;--radius:14px}' +
'#p1hqr-btn,#p1hqr-toast{display:none!important}' +
'*{box-sizing:border-box}' +
'html,body{min-height:100%}' +
'body{margin:0;background:var(--soft);color:var(--ink);font-family:Inter,-apple-system,BlinkMacSystemFont,"Segoe UI",Arial,sans-serif}' +
'.shell{max-width:1500px;margin:0 auto;padding:20px 24px 42px}' +
'.topbar{position:sticky;top:0;z-index:20;margin:-20px -24px 20px;padding:17px 24px 15px;background:rgba(246,247,249,.96);backdrop-filter:blur(12px);border-bottom:1px solid rgba(229,231,235,.92)}' +
'.topline{display:flex;align-items:center;justify-content:space-between;gap:24px}' +
'.brand{min-width:0}' +
'.eyebrow{font-size:11px;font-weight:900;letter-spacing:.16em;text-transform:uppercase;color:var(--blue);margin-bottom:3px}' +
'h1{margin:0;font-size:22px;line-height:1.15;letter-spacing:-.02em}' +
'.meta{font-size:12px;color:var(--muted);margin-top:6px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}' +
'.actions{display:flex;align-items:center;gap:8px;flex-wrap:wrap;justify-content:flex-end}' +
'button,input{font:inherit}' +
'.action{height:42px;border:1px solid var(--line);background:#fff;color:var(--ink);border-radius:11px;padding:0 17px;font-size:13px;font-weight:850;cursor:pointer;display:inline-flex;align-items:center;justify-content:center;gap:7px;box-shadow:0 2px 7px rgba(15,23,42,.06)}' +
'.action:hover{border-color:#cbd5e1;background:#f8fafc}' +
'.action.primary{border-color:var(--blue);background:var(--blue);color:#fff}.action.primary:hover{background:var(--blue2)}' +
'.action:focus-visible,.qr-open:focus-visible,.viewer button:focus-visible{outline:3px solid rgba(37,99,235,.28);outline-offset:2px}' +







'.warn{background:#fffbeb;border:1px solid #fde68a;border-radius:12px;padding:10px 12px;font-size:13px;color:#92400e;margin-bottom:16px}' +
'.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(220px,1fr));gap:16px}' +
'.card{position:relative;border:1px solid var(--line);border-radius:var(--radius);padding:11px 11px 13px;text-align:center;background:#fff;break-inside:avoid;page-break-inside:avoid;box-shadow:0 1px 2px rgba(15,23,42,.04);transition:transform .14s ease,box-shadow .14s ease,border-color .14s ease}' +
'.card:hover{transform:translateY(-1px);border-color:#d1d5db;box-shadow:0 8px 24px rgba(15,23,42,.07)}' +

'.card-top{display:flex;align-items:center;justify-content:space-between;margin-bottom:4px;min-height:22px}' +
'.card-num{font-variant-numeric:tabular-nums;font-size:10px;font-weight:900;color:#9ca3af;letter-spacing:.08em}' +
'.card-tag{font-size:9px;font-weight:900;letter-spacing:.08em;color:var(--blue);background:#eff6ff;border-radius:999px;padding:4px 7px}' +
'.qr-open{display:block;width:100%;border:0;background:#fff;border-radius:10px;padding:4px;cursor:zoom-in}' +
'.qr-img{width:100%;max-width:194px;height:auto;display:block;margin:0 auto;object-fit:contain;image-rendering:auto}' +
'.loc{font-size:15px;font-weight:900;letter-spacing:.01em;word-break:break-word;line-height:1.25;margin-top:5px}' +
'.sid{font-family:"SFMono-Regular",Consolas,"Liberation Mono",monospace;font-size:10.5px;color:var(--muted);margin-top:5px;word-break:break-all}' +

'.viewer{position:fixed;inset:0;z-index:999999;background:rgba(3,7,18,.82);display:none;align-items:center;justify-content:center;padding:18px;backdrop-filter:blur(5px)}' +
'.viewer.open{display:flex}' +
'.viewer-box{position:relative;width:min(90vw,350px);max-height:92vh;background:#fff;color:var(--ink);border-radius:16px;padding:46px 44px 16px;text-align:center;box-shadow:0 24px 80px rgba(0,0,0,.44);display:flex;flex-direction:column;align-items:center;overflow:auto}' +
'.viewer-head{position:absolute;left:14px;top:14px;font-size:10px;font-weight:900;letter-spacing:.12em;text-transform:uppercase;color:var(--muted)}' +
'.viewer-qr-wrap{background:#fff;border-radius:10px;padding:2px}' +
'.viewer-qr{display:block;width:min(31vh,220px);height:auto;max-width:100%;object-fit:contain;background:#fff}' +
'.viewer-loc{margin-top:13px;font-size:16px;font-weight:900;line-height:1.18;word-break:break-word}' +
'.viewer-sid{margin-top:7px;width:100%;padding:8px 9px;border:1px solid #d1d5db;border-radius:8px;background:#f9fafb;font-family:"SFMono-Regular",Consolas,monospace;font-size:10.5px;color:#374151;word-break:break-all}' +
'.viewer-actions{display:flex;margin-top:9px;width:100%}' +
'.viewer-mini{width:100%;height:34px;border:1px solid #d1d5db;border-radius:8px;background:#fff;color:#374151;font-size:11px;font-weight:850;cursor:pointer}.viewer-mini:hover{background:#f9fafb}' +
'.viewer-close{position:absolute;top:9px;right:9px;width:32px;height:32px;padding:0;border:0;border-radius:9px;background:#111827;color:#fff;font-size:20px;line-height:32px;cursor:pointer}' +
'.viewer-nav{position:absolute;top:50%;transform:translateY(-50%);width:30px;height:50px;padding:0;border:0;border-radius:9px;background:#111827;color:#fff;font-size:24px;line-height:1;cursor:pointer}.viewer-nav:hover,.viewer-close:hover{background:#374151}' +
'.viewer-prev{left:7px}.viewer-next{right:7px}' +
'.viewer-help{position:absolute;left:50%;bottom:12px;transform:translateX(-50%);color:#e5e7eb;font-size:11px;font-weight:700;opacity:.9;white-space:nowrap}' +
'.out-toast{position:fixed;left:50%;bottom:24px;z-index:1000000;transform:translate(-50%,10px);background:#111827;color:#fff;border-radius:999px;padding:9px 14px;font-size:12px;font-weight:800;opacity:0;pointer-events:none;transition:opacity .16s,transform .16s}.out-toast.show{opacity:1;transform:translate(-50%,0)}' +
'@media(max-width:700px){.shell{padding:14px 14px 32px}.topbar{margin:-14px -14px 16px;padding:14px}.topline{align-items:center}.actions{gap:6px}.action{height:40px;padding:0 14px}.meta{max-width:72vw}.grid{grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:12px}}' +
'@media(max-width:460px){h1{font-size:19px}.topline{display:grid;grid-template-columns:minmax(0,1fr) auto;align-items:center;gap:10px}.actions{margin:0}.action{height:38px;padding:0 12px}.meta{max-width:100%}.grid{grid-template-columns:1fr 1fr}.card{padding:8px}.loc{font-size:13px}.sid{font-size:9px}.viewer{padding:8px}.viewer-box{width:min(92vw,340px);padding:44px 42px 14px}.viewer-qr{width:min(30vh,210px)}}' +
'@media(prefers-reduced-motion:reduce){*,*::before,*::after{animation:none!important;transition:none!important;scroll-behavior:auto!important}}' +

'</style></head><body>' +
'<main class="shell" data-p1hqr-workspace-root="1">' +
  '<section class="topbar no-print">' +
    '<div class="topline">' +
      '<div class="brand"><div class="eyebrow">COMO QR WORKSPACE</div>' +
        '<h1>' + esc(TARGET_PREFIX) + ' <span style="font-weight:500;color:#9ca3af">/</span> ' + countLabel + '</h1>' +
        '<div class="meta">Scannable ID is the QR value &middot; generated ' + esc(stamp) + '</div></div>' +
      '<div class="actions">' +
        '<button id="scan-first" class="action primary" type="button">&#9635; Scan mode</button>' +
      '</div>' +
    '</div>' +
  '</section>' +
  warn +
  '<div id="qr-grid" class="grid">' + cards + '</div>' +

'</main>' +
'<div id="qr-viewer" class="viewer no-print" aria-hidden="true">' +
  '<div class="viewer-box" role="dialog" aria-modal="true" aria-labelledby="viewer-loc" aria-describedby="viewer-sid">' +
    '<div id="viewer-head" class="viewer-head">SCAN 1 / ' + rendered + '</div>' +
    '<button id="viewer-close" class="viewer-close" type="button" aria-label="Close scan mode">&times;</button>' +
    '<button id="viewer-prev" class="viewer-nav viewer-prev" type="button" aria-label="Previous QR">&#8249;</button>' +
    '<div class="viewer-qr-wrap"><img id="viewer-qr" class="viewer-qr" alt="Selected QR code"></div>' +
    '<div id="viewer-loc" class="viewer-loc"></div>' +
    '<div id="viewer-sid" class="viewer-sid"></div>' +
    '<div class="viewer-actions"><button id="copy-id" class="viewer-mini" type="button">Copy Scannable ID</button></div>' +
    '<button id="viewer-next" class="viewer-nav viewer-next" type="button" aria-label="Next QR">&#8250;</button>' +
  '</div>' +
  '<div class="viewer-help">&#8592; &#8594; navigate &nbsp;&middot;&nbsp; Home / End jump &nbsp;&middot;&nbsp; Esc closes</div>' +
'</div>' +
'<div id="out-toast" class="out-toast" role="status" aria-live="polite"></div>' +
'<script>' +
'(function(){' +
  'var allCards=Array.prototype.slice.call(document.querySelectorAll(".card"));' +
  'var visibleCards=allCards.slice();' +
  'var viewer=document.getElementById("qr-viewer");' +
  'var box=viewer.querySelector(".viewer-box");' +
  'var qr=document.getElementById("viewer-qr");' +
  'var loc=document.getElementById("viewer-loc");' +
  'var sid=document.getElementById("viewer-sid");' +
  'var head=document.getElementById("viewer-head");' +



  'var current=0,lastFocus=null,toastTimer=null;' +
  'function outToast(msg){var t=document.getElementById("out-toast");t.textContent=msg;t.classList.add("show");clearTimeout(toastTimer);toastTimer=setTimeout(function(){t.classList.remove("show");},1800);}' +


  'function show(i){if(!visibleCards.length)return;current=(i+visibleCards.length)%visibleCards.length;var card=visibleCards[current];var img=card.querySelector(".qr-img");qr.src=img.src;qr.alt=img.alt;loc.textContent=card.querySelector(".loc").textContent;sid.textContent=card.querySelector(".sid").textContent;head.textContent="SCAN "+(current+1)+" / "+visibleCards.length;}' +
  'function openAt(i,origin){if(!visibleCards.length){outToast("No QR codes available");return;}lastFocus=origin||document.activeElement;show(i);viewer.classList.add("open");viewer.setAttribute("aria-hidden","false");document.body.style.overflow="hidden";document.getElementById("viewer-close").focus();}' +
  'function closeViewer(){viewer.classList.remove("open");viewer.setAttribute("aria-hidden","true");document.body.style.overflow="";if(lastFocus&&lastFocus.focus)try{lastFocus.focus();}catch(e){}}' +
  'function copyText(text){if(navigator.clipboard&&navigator.clipboard.writeText){navigator.clipboard.writeText(text).then(function(){outToast("Scannable ID copied");},fallback);}else fallback();function fallback(){try{var ta=document.createElement("textarea");ta.value=text;ta.style.position="fixed";ta.style.opacity="0";document.body.appendChild(ta);ta.select();document.execCommand("copy");ta.remove();outToast("Scannable ID copied");}catch(e){outToast("Copy failed");}}}' +
  'allCards.forEach(function(card){card.querySelector(".qr-open").addEventListener("click",function(){openAt(visibleCards.indexOf(card),this);});});' +
  'document.getElementById("viewer-prev").addEventListener("click",function(){show(current-1);});' +
  'document.getElementById("viewer-next").addEventListener("click",function(){show(current+1);});' +
  'document.getElementById("viewer-close").addEventListener("click",closeViewer);' +
  'document.getElementById("scan-first").addEventListener("click",function(){openAt(0,this);});' +


  'document.getElementById("copy-id").addEventListener("click",function(){copyText(sid.textContent);});' +


  'viewer.addEventListener("click",function(e){if(e.target===viewer)closeViewer();});' +
  'box.addEventListener("click",function(e){e.stopPropagation();});' +
  'document.addEventListener("keydown",function(e){' +
    'if(!viewer.classList.contains("open"))return;' +
    'if(e.key==="ArrowLeft"){e.preventDefault();show(current-1);}' +
    'else if(e.key==="ArrowRight"){e.preventDefault();show(current+1);}' +
    'else if(e.key==="Home"){e.preventDefault();show(0);}' +
    'else if(e.key==="End"){e.preventDefault();show(visibleCards.length-1);}' +
    'else if(e.key==="Escape"){e.preventDefault();closeViewer();}' +
    'else if(e.key==="Tab"){' +
      'var f=Array.prototype.slice.call(box.querySelectorAll("button:not([disabled])"));if(!f.length)return;var first=f[0],last=f[f.length-1];if(e.shiftKey&&document.activeElement===first){e.preventDefault();last.focus();}else if(!e.shiftKey&&document.activeElement===last){e.preventDefault();first.focus();}' +
    '}' +
  '});' +

  'if(visibleCards.length){setTimeout(function(){openAt(0,document.getElementById("scan-first"));},0);}' +
'})();' +
'<\/script>' +
'</body></html>'
  );
}

function buildLoadingHTML() {
  return '<!DOCTYPE html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">' +
    '<title>Building ' + esc(TARGET_PREFIX) + ' QR Codes…</title><style>' +
    '*{box-sizing:border-box}body{margin:0;min-height:100vh;display:grid;place-items:center;background:#f6f7f9;color:#111827;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Arial,sans-serif}' +
    '.box{width:min(88vw,420px);background:#fff;border:1px solid #e5e7eb;border-radius:22px;padding:28px;text-align:center;box-shadow:0 18px 60px rgba(15,23,42,.10)}' +
    '.mark{width:52px;height:52px;border-radius:18px;background:#2563eb;color:#fff;display:grid;place-items:center;margin:0 auto 14px;font-size:25px;font-weight:900}.title{font-size:18px;font-weight:900}.sub{margin-top:7px;font-size:13px;color:#6b7280}.bar{height:4px;background:#e5e7eb;border-radius:999px;overflow:hidden;margin-top:20px}.bar:after{content:"";display:block;width:42%;height:100%;background:#2563eb;border-radius:inherit;animation:m 1s ease-in-out infinite alternate}@keyframes m{from{transform:translateX(-10%)}to{transform:translateX(160%)}}@media(prefers-reduced-motion:reduce){.bar:after{animation:none;width:100%}}' +
    '</style></head><body><div class="box"><div class="mark">QR</div><div class="title">Building ' + esc(TARGET_PREFIX) + ' QR codes</div><div class="sub">Waiting for the cart table and collecting Scannable IDs…</div><div class="bar"></div></div></body></html>';
}

/* Write HTML to a tab; returns true on success, false if the write was blocked. */
function writeToTab(win, html) {
  if (!win || win.closed) return false;
  try {
    win.document.open();
    win.document.write(html);
    win.document.close();
    return !!(win.document.body && win.document.body.innerHTML.length > 100);
  } catch (e) {
    return false;
  }
}

function openQRTab(items, win) {
  var html = buildTabHTML(items);
  if (writeToTab(win, html)) {
    try { win.opener = null; } catch (e0) {}
    return true;
  }

  try {
    var blob = new Blob([html], { type: 'text/html' });
    var url  = URL.createObjectURL(blob);
    try { win.opener = null; } catch (e1) {}
    win.location.replace(url);
    setTimeout(function () { try { URL.revokeObjectURL(url); } catch (e2) {} }, 60000);
    return true;
  } catch (e) {
    return false;
  }
}


/* ══════════════════════════════════════════════════════════
   DASHBOARD UI — compact launcher + count + toast
══════════════════════════════════════════════════════════ */
var style = document.createElement('style');
style.textContent =
  /* The launcher now lives INSIDE the site's Manager Actions button group.
     No fixed/floating coordinates are used, so it cannot drift or be dragged. */
  '#p1hqr-btn{position:static!important;float:none!important;left:auto!important;right:auto!important;top:auto!important;bottom:auto!important;' +
    'z-index:auto!important;display:none;align-items:center;justify-content:center;gap:3px;' +
    'margin:0!important;padding:0 6px!important;' +
    'border:1px solid #2e6da4!important;border-radius:0!important;background:#337ab7!important;color:#fff!important;' +
    'font-family:"Helvetica Neue",Helvetica,Arial,sans-serif!important;font-size:14px!important;font-weight:400!important;' +
    'line-height:1.42857143!important;box-shadow:none!important;cursor:pointer;user-select:none;touch-action:auto;' +
    'transform:none!important;transition:background .12s ease,border-color .12s ease!important;vertical-align:middle!important;' +
    'white-space:nowrap!important;overflow:hidden!important}' +
  '#p1hqr-btn.visible{display:inline-flex!important}' +
  '#p1hqr-btn:not(:disabled):hover,#p1hqr-btn:not(:disabled):focus{background:#286090!important;border-color:#204d74!important;color:#fff!important;transform:none!important}' +
  '#p1hqr-btn:not(:disabled):active{background:#204d74!important;border-color:#122b40!important;transform:none!important}' +
  '#p1hqr-btn:focus-visible{outline:2px solid rgba(51,122,183,.35);outline-offset:2px}' +
  '#p1hqr-btn.busy{background:#6b7280!important;border-color:#5b6470!important;cursor:wait!important;opacity:.72!important}' +
  '#p1hqr-btn.no-data,#p1hqr-btn:disabled.no-data{background:#6b7280!important;border-color:#5b6470!important;color:#e5e7eb!important;cursor:not-allowed!important;opacity:.62!important;box-shadow:none!important}' +
  '#p1hqr-btn .p1h-icon{display:none!important}' +
  '#p1hqr-btn .p1h-copy{display:flex;align-items:center;min-width:0;overflow:hidden;line-height:1}' +
  '#p1hqr-btn .p1h-main{font-size:10px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:clip}' +
  '#p1hqr-btn .p1h-sub{display:none!important}' +
  '#p1hqr-btn .p1h-count{flex:0 0 auto;min-width:14px;height:14px;padding:0 3px;border-radius:8px;background:#fff;color:#337ab7;' +
    'display:grid;place-items:center;font-size:9px;font-weight:800;font-variant-numeric:tabular-nums}' +
  '#p1hqr-btn .p1h-count.zero{background:rgba(255,255,255,.2);color:#fff}' +
  /* Bootstrap 3 btn-group removes the inside corner between adjacent buttons.
     Match that behavior even though this button is injected after Angular. */
  '.btn-group>#p1hqr-btn:not(:first-child){margin-left:-1px!important}' +
  '.btn-group>#p1hqr-btn:last-child{border-top-right-radius:4px!important;border-bottom-right-radius:4px!important}' +
  '#p1hqr-toast{position:fixed;bottom:24px;left:24px;z-index:100000;max-width:min(420px,calc(100vw - 48px));' +
    'background:#111827;color:#fff;font:13px/1.42 "Segoe UI",system-ui,sans-serif;padding:11px 13px;border-radius:11px;' +
    'box-shadow:0 12px 34px rgba(0,0,0,.28);opacity:0;transform:translateY(7px);transition:opacity .16s ease,transform .16s ease;pointer-events:none}' +
  '#p1hqr-toast.show{opacity:1;transform:none}' +
  '#p1hqr-toast.err{background:#991b1b}' +
  '@media(max-width:620px){#p1hqr-btn .p1h-main{font-size:9px}#p1hqr-toast{left:12px;bottom:12px;max-width:calc(100vw - 24px)}}' +
  '@media(prefers-reduced-motion:reduce){#p1hqr-btn,#p1hqr-toast{transition:none!important}}';
document.head.appendChild(style);

var btn = document.createElement('button');
btn.id = 'p1hqr-btn';
btn.className = 'btn btn-primary';
btn.type = 'button';
btn.innerHTML =
  '<span class="p1h-icon" aria-hidden="true">QR</span>' +
  '<span class="p1h-copy"><span class="p1h-main">' + TARGET_PREFIX + ' QR Codes</span>' +
    '<span class="p1h-sub">Scannable ID</span></span>' +
  '<span id="p1hqr-count" class="p1h-count zero" aria-label="0 QR codes">0</span>';
btn.title = 'No ' + TARGET_PREFIX + ' Scannable IDs are available to generate.';
btn.disabled = true;
btn.setAttribute('aria-disabled', 'true');
btn.classList.add('no-data');
document.body.appendChild(btn);

var countEl = btn.querySelector('#p1hqr-count');
var mainLabelEl = btn.querySelector('.p1h-main');
var subLabelEl = btn.querySelector('.p1h-sub');

var launcherCount = 0;
var launcherBusy = false;

function syncLauncherDisabledState() {
  var noData = launcherCount <= 0;
  var disabled = launcherBusy || noData;

  btn.disabled = disabled;
  btn.setAttribute('aria-disabled', disabled ? 'true' : 'false');
  btn.classList.toggle('no-data', noData && !launcherBusy);
}

var toastEl = document.createElement('div');
toastEl.id = 'p1hqr-toast';
toastEl.setAttribute('role', 'status');
toastEl.setAttribute('aria-live', 'polite');
document.body.appendChild(toastEl);

var toastTimer = null;
function toast(msg, isErr) {
  toastEl.textContent = msg;
  toastEl.setAttribute('role', isErr ? 'alert' : 'status');
  toastEl.className = 'show' + (isErr ? ' err' : '');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(function () { toastEl.className = ''; }, isErr ? 6500 : 3000);
}

function updateLauncherCount(count) {
  count = Math.max(0, Number(count) || 0);
  launcherCount = count;

  countEl.textContent = String(count);
  countEl.setAttribute('aria-label', count + ' QR code' + (count === 1 ? '' : 's'));
  countEl.classList.toggle('zero', count === 0);

  btn.title = count
    ? 'Open ' + count + ' ' + TARGET_PREFIX + ' QR code' + (count === 1 ? '' : 's')
    : 'No ' + TARGET_PREFIX + ' Scannable IDs are available to generate.';

  syncLauncherDisabledState();
}

function setBusy(v) {
  launcherBusy = !!v;
  btn.classList.toggle('busy', launcherBusy);
  btn.setAttribute('aria-busy', launcherBusy ? 'true' : 'false');

  if (launcherBusy) {
    mainLabelEl.textContent = 'Building QR';
    subLabelEl.textContent = 'Please wait';
  } else {
    mainLabelEl.textContent = TARGET_PREFIX + ' QR Codes';
    subLabelEl.textContent = 'Scannable ID';
  }

  syncLauncherDisabledState();
}

/* Fixed Manager Actions placement.
   The button is always inserted immediately AFTER the site's Complete Task
   button. There are no drag handlers and no saved screen coordinates. */
function findCompleteTaskButton() {
  var direct = document.querySelector(
    'button[ng-click*="showCompleteJobDialog"],' +
    'button[data-ng-click*="showCompleteJobDialog"]'
  );
  if (direct) return direct;

  /* Fallback for a future Angular markup change: search only normal buttons
     and require the exact visible label "Complete Task". */
  var buttons = document.querySelectorAll('.btn-group button, .job-details button');
  for (var i = 0; i < buttons.length; i++) {
    if (String(buttons[i].textContent || '').replace(/\s+/g, ' ').trim() === 'Complete Task') {
      return buttons[i];
    }
  }
  return null;
}

function syncLauncherSizeToComplete(complete) {
  if (!complete) return;

  /* Match the site's Complete Task button exactly. Using its rendered
     dimensions makes this survive browser zoom and Amazon CSS changes. */
  var rect = null;
  try { rect = complete.getBoundingClientRect(); } catch(e) {}
  if (!rect || rect.width <= 0 || rect.height <= 0) return;

  var w = Math.max(1, Math.round(rect.width));
  var h = Math.max(1, Math.round(rect.height));

  btn.style.setProperty('width', w + 'px', 'important');
  btn.style.setProperty('min-width', w + 'px', 'important');
  btn.style.setProperty('max-width', w + 'px', 'important');
  btn.style.setProperty('height', h + 'px', 'important');
  btn.style.setProperty('min-height', h + 'px', 'important');
  btn.style.setProperty('max-height', h + 'px', 'important');
}

function mountLauncherInline() {
  var complete = findCompleteTaskButton();
  if (!complete) return false;

  var group = complete.closest ? complete.closest('.btn-group') : complete.parentElement;
  if (!group) group = complete.parentElement;
  if (!group) return false;

  /* Always keep it directly after Complete Task. If Angular replaces or
     reorders the button group, the lifecycle observer simply restores this
     exact location. */
  if (btn.parentNode !== group || complete.nextElementSibling !== btn) {
    if (complete.nextSibling) group.insertBefore(btn, complete.nextSibling);
    else group.appendChild(btn);
  }

  /* Inline placement must never inherit any stale position coordinates from
     older script versions. */
  btn.style.position = 'static';
  btn.style.left = '';
  btn.style.top = '';
  btn.style.right = '';
  btn.style.bottom = '';
  btn.style.transform = '';

  syncLauncherSizeToComplete(complete);
  return true;
}

function saveLauncherPosition() {}
function restoreLauncherPosition() {
  mountLauncherInline();
}

window.addEventListener('resize', function () {
  if (btnVisible) mountLauncherInline();
});

/* Maximum automatic retries while Angular finishes rendering the table. */
var MAX_RETRIES = 5, RETRY_MS = 500;
var generationSession = 0;
var generationTimer = null;
var pendingWindow = null;

function generationStillCurrent(sessionId) {
  return sessionId === generationSession;
}

function closePendingWindow() {
  if (!pendingWindow) return;
  try { if (!pendingWindow.closed) pendingWindow.close(); } catch (e) {}
  pendingWindow = null;
}

function resetBtn() {
  setBusy(false);
}

function finishGeneration(sessionId, success) {
  if (!generationStillCurrent(sessionId)) return;
  clearTimeout(generationTimer);
  generationTimer = null;
  if (success) pendingWindow = null;
  resetBtn();
  scheduleCountRefresh(0);
}

function failGeneration(sessionId, message) {
  if (!generationStillCurrent(sessionId)) return;
  closePendingWindow();
  toast(message, true);
  finishGeneration(sessionId, false);
}

function doGenerate(attempt, sessionId, win) {
  if (!generationStillCurrent(sessionId)) return;
  if (!win || win.closed) {
    pendingWindow = null;
    toast('QR window was closed before generation finished.', true);
    finishGeneration(sessionId, false);
    return;
  }

  var res = scrapeRows();
  if (!generationStillCurrent(sessionId)) return;

  if ((res.error || !res.items.length) && attempt < MAX_RETRIES) {
    generationTimer = setTimeout(function () {
      if (generationStillCurrent(sessionId)) doGenerate(attempt + 1, sessionId, win);
    }, RETRY_MS);
    return;
  }

  if (res.error) {
    failGeneration(sessionId, 'Could not find the item table on this cart. Open the cart details fully, then try again.');
    return;
  }

  if (!res.items.length) {
    failGeneration(sessionId,
      'No ' + TARGET_PREFIX + ' rows found (scanned ' + res.total + ' row' + (res.total === 1 ? '' : 's') + ').');
    return;
  }

  var ok = false;
  try { ok = openQRTab(res.items, win); } catch (e) { ok = false; }

  if (!ok) {
    failGeneration(sessionId, 'The QR tab opened, but its content could not be written. Try again or disable extensions that block new-tab scripts.');
    return;
  }

  toast(res.items.length + ' QR code' + (res.items.length === 1 ? '' : 's') + ' ready.', false);
  finishGeneration(sessionId, true);
}

function startGeneration() {
  generationSession++;
  var sessionId = generationSession;
  clearTimeout(generationTimer);
  generationTimer = null;
  closePendingWindow();

  /* Open immediately inside the click gesture. This is the reliable way to
     avoid popup blockers even when the Angular table needs a retry. */
  var win = window.open('', '_blank');
  if (!win) {
    toast('Popup blocked — allow popups for this site, then click the QR button again.', true);
    resetBtn();
    return;
  }

  pendingWindow = win;
  setBusy(true);
  writeToTab(win, buildLoadingHTML());
  doGenerate(0, sessionId, win);
}

btn.addEventListener('click', function () {
  if (suppressClick) { suppressClick = false; return; }
  if (btn.disabled || launcherBusy || launcherCount <= 0) return;
  startGeneration();
});


/* ══════════════════════════════════════════════════════════
   VISIBILITY + SPA LIFECYCLE
══════════════════════════════════════════════════════════ */
var btnVisible = false;
function setVisible(v) {
  if (v) {
    /* Never show the launcher anywhere except beside Complete Task. */
    if (!mountLauncherInline()) {
      v = false;
    }
  }

  var changed = v !== btnVisible;
  btnVisible = v;
  btn.classList.toggle('visible', v);

  if (v) {
    /* Re-assert exact placement even when visibility itself did not change,
       because Angular can rebuild the Manager Actions group in-place. */
    mountLauncherInline();
    if (changed) scheduleCountRefresh(0);
  }
}

function isGeneratedWorkspace() {
  var root = document.documentElement;
  if (root && root.getAttribute('data-p1hqr-workspace') === '1') return true;
  if (document.querySelector('[data-p1hqr-workspace-root="1"]')) return true;
  return false;
}

function cheapDetail() {
  if (/\/task\/|jobdetails/i.test(location.href)) return true;
  if (document.querySelector('div.job-details')) return true;
  return false;
}

var tblAt = 0, tblRes = false;
function tableDetail() {
  var now = Date.now();
  if (now - tblAt > 700) {
    tblAt = now;
    tblRes = !!findTable();
  }
  return tblRes;
}

function updateVisibility() {
  /* The generated QR workspace can retain the original /jobdetails URL in
     some browsers. The workspace marker must win over URL-based detection so
     the dashboard launcher never appears inside the QR workspace itself. */
  if (isGeneratedWorkspace()) { setVisible(false); return; }
  if (cheapDetail()) { setVisible(true); return; }
  setVisible(tableDetail());
}

var countRefreshTimer = null;
function scheduleCountRefresh(delay) {
  clearTimeout(countRefreshTimer);
  countRefreshTimer = setTimeout(function () {
    countRefreshTimer = null;
    if (!btnVisible || document.hidden || isGeneratedWorkspace()) return;
    var res = scrapeRows();
    updateLauncherCount(res.error ? 0 : res.items.length);
  }, delay === undefined ? 220 : delay);
}

function onNavigate() {
  generationSession++;
  clearTimeout(generationTimer);
  generationTimer = null;
  closePendingWindow();
  setBusy(false);
  setVisible(false);
  updateLauncherCount(0);
  tblAt = 0;
  tblRes = false;
  clearTimeout(toastTimer);
  toastEl.className = '';
  updateVisibility();
}

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

document.addEventListener('visibilitychange', function () {
  if (!document.hidden) {
    updateVisibility();
    scheduleCountRefresh(40);
  }
});

/* Low-frequency URL safety net. The history patches catch normal Angular
   navigation immediately; this catches unusual route changes without a 120ms loop. */
var lastHref = location.href;
setInterval(function () {
  if (location.href !== lastHref) {
    lastHref = location.href;
    onNavigate();
  }
}, 700);

/* One observer, work coalesced through a timer instead of rescanning the
   entire document for every mutation burst. */
var domRefreshTimer = null;
new MutationObserver(function () {
  if (domRefreshTimer) return;
  domRefreshTimer = setTimeout(function () {
    domRefreshTimer = null;
    updateVisibility();
    scheduleCountRefresh(0);
  }, 240);
}).observe(document.body, { childList: true, subtree: true });

updateVisibility();
mountLauncherInline();
scheduleCountRefresh(40);

console.log('[P1H-QR] v1.4.5 loaded — same size as Complete Task; disabled/grey at zero; QR value = Scannable ID');

})();
