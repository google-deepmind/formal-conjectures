# Fifteenth Krein cell: derivative-free direct closure

Serialized cell index 14 of the order-19 L = 4/5 Krein certificate,
`[2475/32768, 1275/16384]`, `lower64 = 292616690003685633`.

The zero-centred jet route is falsified on this cell (endpoint budget
≈ −5.06·10⁻⁴), and the midpoint reduction `RHKreinFifteenthCellReductionV1`
left seven jet enclosures (`k = 1..7`) open. This slice closes the cell without
any jet, any derivative of the correction symbol, or the M8 remainder.

## Method

For `t = c + s` with `c = 5025/65536`, `|s| ≤ 75/65536`:

* `cos((c+s)h) = cos(ch)·cos(sh) − sin(ch)·sin(sh)` for every hat column and the
  edge phase; `cos(ch)`, `sin(ch)` are enclosed by degree-15 Taylor polynomials
  (error ≤ 10⁻²⁰ on `|x| ≤ 3/8`) rounded to `10⁻²⁴`; `cos(sh)`, `sin(sh)` by
  degree-7 polynomials (error ≤ 10⁻²⁰ on `|y| ≤ 1/100`).
* `sinc(x)^m = 1 − m·x²/6 + θ` with `|θ| ≤ m·x⁴/100 + m²·(x²/6)²/2`
  (`sinc_quad`, `pow_quad`), for `m = 2, 19`.
* The correction symbol is then a degree-13 rational polynomial `G(s)` plus an
  explicit error ≤ 5.8·10⁻⁸; the sign-independent floor
  `g₀ − Σ_{k≥1} |g_k| r^k` exceeds the cell requirement by ≈ 3.63·10⁻⁵.

## Kernel result (local replay)

```
AEGIS.RHKreinFifteenthCellDirectCorrectionV1.correction_lower_direct : [propext, Classical.choice, Quot.sound]
AEGIS.RHKreinFifteenthCellDirectV1.fifteenthCell_sound_direct        : [propext, Classical.choice, Quot.sound]
AEGIS.RHKreinFifteenthCellDirectV1.first_fifteen_cells_sound         : [propext, Classical.choice, Quot.sound]
```

Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
`RHKreinFifteenthCellDirectCorrectionV1` compiles in ≈ 34 min (one core); the
cell theorem in 12 s.

| file | SHA-256 |
|---|---|
| `RHKreinFifteenthCellDirectCorrectionV1.lean` | `0d3845e40e1079b395cec3b172d33f5ca1b966315513c1ebcb19262fc09cf82f` |
| `RHKreinFifteenthCellDirectV1.lean` | `93e9b601049ec0ab0bc592425454b949c4270f78d19fb7fe832636d0a6b886ba` |
| `RHKreinFifteenthCellDirectCorrectionV1.olean` | `a56f92f24daa213fcb7ced1ebf7377004f337b5648c9ccc3f85f368538e1749a` |
| `RHKreinFifteenthCellDirectV1.olean` | `2fb8c1b355c08e1e0c2e949062bfac54045beb0b24e28de4fe9bc34103a34a0a` |

## Dependency closure

`RHKreinFifteenthCellDirectCorrectionV1` imports only
`AEGISOverlay.RHKreinExplicitCorrectionV1` and
`AEGISOverlay.RHKreinFiniteIntervalKernelV1`. The overlay explicit-correction
module used is the PR #47 blob `eaec6e0` with the one-line compact-support
repair (`HasCompactSupport.addSubmonoid … sum_mem`); replayed file SHA-256
`7b74b68bed4af27179b607e989df445b16453c88aaeeb82cbe978a52caf6930a`.

`RHKreinFifteenthCellDirectV1` additionally imports
`RHKreinFifteenthCellReductionV1` (for `fifteenthCell`, its symbol floor and
weight bound) and, through it, cells 1–14. Those modules come from the archive
`AEGIS_PR53_first_cell_reduction.zip` (SHA-256
`2adc193dbac0035238970bb25f71ec80ac8df96b288d065c2a80ea12734ad98c`), whose
127-module closure was replayed locally with only the standard axioms.

## Regeneration

```
EXPLICIT_CORRECTION=path/to/AEGISOverlay/RHKreinExplicitCorrectionV1.lean \
  python3 gen.py RHKreinFifteenthCellDirectCorrectionV1.lean
```

reproduces the module byte-for-byte (SHA-256 above). The generated
`RHKreinFifteenthCellDirectCorrectionV1.lean` (66 KB, mostly rounded tables) is
not committed by hand; generate it into `research/rh/m8_kernel_v1/` before
building `RHKreinFifteenthCellDirectV1`. `model.py` holds the exact-rational model
(tables, polynomial coefficients, error budget) and is the input to `gen.py`.

## Scope

This closes one serialized cell of one window (L = 4/5). It does not prove the
remaining 2,184 cells, the tail `t ≥ 300`, the certificate-to-window bridge,
any other window, global Weil positivity, or the Riemann hypothesis.
AUTHORITY_EFFECT = NONE.
