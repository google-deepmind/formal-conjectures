# Controlled A2 and spline-pattern tests

This packet tests two operator hypotheses against exact finite calculations and
controlled numerical discovery. It contains no new RH proof assumption.

## Same-width spline comparison

`compare_orders.py` reuses the basis and symbol of the baseline
`krein_order19_v1/regenerate.py`. The total spline support remains `19/1000`,
its center remains `1619/2000`, the forbidden half-window remains `4/5`, and
all cases use the same 199 hats, derivative columns 0 through 4, coefficient
cap `10^5`, LP grid `[0,300)` with step `1/50`, and diagnostic grid `[0,3000)`
with step `1/500`. Every profile has integral one. Changing order changes the
knot step to `19/(1000*order)`, rather than accidentally changing the width.

| Profile | LP margin | Diagnostic grid minimum | Normalized five-edge-column condition |
| --- | ---: | ---: | ---: |
| Order 17 | 0.0939978854 | 0.0939686927 | 13.45347 |
| Order 18 | 0.0939956414 | 0.0939651485 | 13.45275 |
| Order 19 | 0.0939936338 | 0.0939619807 | 13.45211 |
| Order 20 | 0.0939918269 | 0.0939591239 | 13.45154 |
| Order 21 | 0.0939901921 | 0.0939565433 | 13.45101 |
| A2 axis projection | 0.0940004101 | 0.0939726791 | 13.45427 |
| A2 30-degree projection | 0.0940147138 | 0.0939850769 | 13.45880 |

Order 19 is not exceptional in this comparison. The small changes do not justify
attributing the performance to the integer 19. These are floating-point LP/grid
results, not certified inequalities, rigorous order rankings, or Weil theorems.
The condition numbers cover only the five edge columns, not the full LP matrix.
The JSON records every discovered coefficient and the software versions.

## Exact projection mechanism and limitation

Let `U_j` be independent uniform random variables on `[-1/2,1/2]` and let the
centered box spline be the distribution of `sum_j U_j*v_j`. Projecting onto a
line with unit direction `e` gives `sum_j U_j*(e dot v_j)`. Its angular Fourier
transform is therefore

`product_j sinc(t*(e dot v_j)/2)`.

This identity follows directly by multiplying the one-segment integrals.
It needs no Wiener theorem. Zero projected directions contribute the constant
factor one. Nonzero projected directions contribute their sinc zero lattices;
**a product retains their union**, so a single projected generator does not
remove transform zeros. Two separate generators instead test the intersection
of their zero sets.

For the directions at 0, 60 and 120 degrees, each repeated six times, projection
onto the horizontal axis gives lengths `delta, delta/2, delta/2` repeated six
times. With `delta=(19/1000)/12` their total support is `19/1000`. Projection at
30 degrees leaves twelve equal nonzero lengths after width normalization, so
it is exactly a cardinal order-12 profile. The two experiments consequently
introduce no mysterious higher-dimensional advantage.

A nonzero positive-definite correction cannot vanish throughout the forbidden
window: positive definiteness gives `|H(x)| <= H(0)`, while `H(0)=0` is required.
This obstruction does not apply to the signed correction H in the Krein LP.

## Nineteen-point exact control

`structure_checks.py` uses standard-library integer/rational arithmetic and
writes `structure_receipt.json`. It verifies:

- A2 graph shells of radius 0, 1 and 2 have sizes 1, 6 and 12.
- `1+3*n*(n+1) = (n+1)^2+(n+1)*n+n^2` as a polynomial coefficient identity.
  Thus the centered count 19 is also the Eisenstein norm `Q_A2(3,2)`.
- The forms `x^2+xy+y^2` and `x^2+xy+5*y^2` have discriminants -3 and -19,
  and six and two proper integral automorphisms respectively. Enumeration is
  complete: completing the square bounds both coordinates of both columns by
  4 for their required norms 1 and c, with c in {1,5}.
- The 19-point stencil autocorrelation has coefficient 19 at the origin and
  Fourier value 9 at `(pi,0)`. Deleting its origin coefficient produces -10.
- Its horizontal projection has stencil coefficients `[3,4,5,4,3]`, origin
  autocorrelation coefficient 75, and Fourier value 9 at pi. Deleting that
  origin coefficient produces -66.

Therefore deleting the central part of this natural positive kernel to force
a forbidden window destroys positivity. These exact finite controls do not
exclude signed spline corrections or prove any assertion about the actual
Weil quadratic. No Lean kernel authority is assigned to the Python receipt.

## Replay

```sh
python research/rh/pattern_phase2/structure_checks.py
OPENBLAS_NUM_THREADS=1 python research/rh/pattern_phase2/compare_orders.py
```

The recorded numerical environment is NumPy 2.3.5, SciPy 1.17.0. HiGHS may pick
a different optimum under another version. Exact structure checks need only
Python's standard library.

## Bounded repository search

`repository_search_receipt.json` records exact inspected refs and coverage.
The earlier half-width 1/8 and 9/64 Lean window producers remain finite-window
results. The Coq globalization theorem consumes convergence and lower bounds;
it does not produce them. The prior Arb moment-restriction implementation
explicitly leaves the actual moment-basis identification unformalized.
No new unconditional producer was found in these inspected sources. This is
not an exhaustive search of all historical branches, languages or artifacts.

## Primary mathematical references

- Carl de Boor and Klaus Höllig, *Box-Spline Tilings* (1991),
  https://ftp.cs.wisc.edu/Approx/boxtiling.pdf . Its appendix supplies the
  product-sinc Fourier convention for box splines.
- Minho Kim and Jörg Peters, *A Practical Box Spline Compendium* (2023),
  https://arxiv.org/abs/2304.04799 . Source for the lattice/symmetry framework.
- Bin Han, Tao Li and Xiaosheng Zhuang, *Directional Compactly supported Box
  Spline Tight Framelets with Simple Structure* (2017),
  https://arxiv.org/abs/1708.08421 . Establishes constructive projection-based
  framelet machinery; no RH claim or transfer theorem is inferred from it.
- LMFDB, number field 2.0.19.1,
  https://www.lmfdb.org/NumberField/2.0.19.1 . Records discriminant -19,
  class number one and a torsion unit group of order two.
