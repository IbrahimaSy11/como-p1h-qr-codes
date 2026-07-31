# COMO P-1-H Scannable ID QR Codes

A Tampermonkey userscript for the COMO Operations Dashboard. On a cart/task detail
page it finds every row whose **Last Known Location** starts with `P-1-H`, then opens
a printable tab of QR codes — one per row — each encoding that row's **Scannable ID**.

> The QR value is always the **Scannable ID**, never the location text.
>
> | Last Known Location | Scannable ID           | QR encodes             |
> |---------------------|------------------------|------------------------|
> | `P-1-H209A190`      | `PHQLR2XLWJGTG5WKDGBC` | `PHQLR2XLWJGTG5WKDGBC` |

---

## Install

**1. Install Tampermonkey** for your browser:
[Chrome](https://chromewebstore.google.com/detail/tampermonkey/dhdgffkkebhmkfjojejmpbldmpobfkfo) ·
[Edge](https://microsoftedge.microsoft.com/addons/detail/tampermonkey/iikmkjmpaadaobahmlepeloendndfphd) ·
[Firefox](https://addons.mozilla.org/firefox/addon/tampermonkey/)

**2. Click the install link:**

### → [Install the script](https://raw.githubusercontent.com/IbrahimaSy11/como-p1h-qr-codes/main/como-p1h-qr-codes.user.js)

Tampermonkey will open its install page — click **Install**. That's it.

Auto-updates are enabled, so Tampermonkey will pick up new versions on its own.

> The script only activates on the COMO dashboard host. You need access to that
> internal dashboard for it to do anything.

---

## Usage

1. Open a cart / task detail page — the one with the **Scannable ID** and
   **Last Known Location** columns.
2. A blue **`⌘ QR: P-1-H`** button appears at the bottom-left. It only shows on
   that page and disappears as soon as you navigate away.
3. Click it. A new tab opens with a printable grid of QR codes.
4. Hit **Print** in that tab (the button hides itself when printing).

Each card shows the QR code, the location in bold underneath, and the Scannable ID
in small text below it — so you can verify the code matches before scanning.

Duplicate rows are collapsed: if the same location *and* Scannable ID appear more
than once, you get one QR code, not two.

---

## Configuration

Edit these near the top of the script (Tampermonkey → Edit):

| Setting | Default | What it does |
|---|---|---|
| `TARGET_PREFIX` | `'P-1-H'` | Location prefix to match. Matching is case-insensitive and anchored to the start. |
| `ECC_LEVEL` | `'M'` | QR error correction: `L` < `M` < `Q` < `H`. Raise to `'Q'` or `'H'` for more tolerance of scuffed or partly covered labels. |
| `MODULE_PX` | `8` | Pixels per QR module. Higher = larger, crisper print. |
| `QUIET_ZONE` | `4` | Quiet-zone border in modules. 4 is the spec minimum — lowering it can break scanning. |

---

## Troubleshooting

**"Could not find a table containing both a Last Known Location and a Scannable ID column"**

The script reads a real HTML `<table>` and locates the two columns by their header
text, so column order doesn't matter. If the page builds its grid from `<div>`s
instead, this message appears. It deliberately fails loudly rather than guessing —
a wrong QR code scanned onto the wrong package is worse than no QR code. Open an
issue with the row markup from DevTools and it can be adapted.

**"No rows found with a Last Known Location starting with P-1-H"**

The table was read fine, but no row matched. The message includes how many rows were
scanned, so if that count looks too low the table may be paginated or virtualised —
only rendered rows are readable.

**Button doesn't appear** — confirm you're on the detail page, not the main dashboard.

**"Popup blocked"** — allow popups for the dashboard host and click again.

---

## About the QR encoder

The QR encoder is built into the script rather than pulled from a CDN. The dashboard
sits behind a corporate proxy, and a blocked external library would make the script
fail silently.

Because a bad QR code is worse than no QR code, the encoder was verified before
release:

- Every generated matrix compared **bit-for-bit** against the
  [`qrcode`](https://www.npmjs.com/package/qrcode) reference implementation.
- **3000+** generated codes decoded back with the
  [jsQR](https://www.npmjs.com/package/jsqr) decoder — 100% pass, all 8 mask
  patterns exercised.

That process caught two real bugs that would have produced unscannable codes:
wrong format-info bit placement, and swapped multiply terms in the Reed–Solomon
generator polynomial (which corrupted every error-correction codeword while the
data codewords looked perfectly fine).

Encoder specs: byte mode, QR versions 1–10, capacity 213 characters at ECC `M`
(119 at `H`) — comfortable headroom over a ~20-character Scannable ID.

---

## License

MIT — see [LICENSE](LICENSE).
