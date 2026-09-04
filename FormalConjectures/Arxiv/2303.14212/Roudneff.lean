/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# The Roudneff conjecture on complete cells of pseudohyperplane arrangements

An *arrangement* of `n` pseudohyperplanes in projective `d`-space `ℙ^d` cuts the
space into cells. A cell is *complete* if it is bounded by **all** `n` of the
pseudohyperplanes. Equivalently, on the oriented-matroid side, a complete cell is a
*tope* `T` (a maximal covector) such that flipping `T` at any single coordinate
again gives a tope. This is strictly stronger than a *simplicial cell* / *mutation*,
which is bounded by exactly `d + 1` hyperplanes (a simplex): a complete cell need not
be a simplex, and a simplicial cell is generally not complete. Roudneff [Rou91]
conjectured a sharp upper bound on the number of complete cells; the paper at
arXiv:2303.14212 extends the conjecture to arrangements of pseudohyperplanes
(equivalently, to rank-`(d+1)` oriented matroids) and studies it there.

**Conjecture 1.1 (Roudneff).** Every arrangement of `n ≥ 2d + 1 ≥ 5`
pseudohyperplanes in `ℙ^d` has at most `∑_{i=0}^{d-2} binomial(n-1, i)` complete
cells.

We phrase this over *oriented matroids* via their **chirotopes**, using the shared
definitions in `FormalConjecturesForMathlib.Combinatorics.OrientedMatroid.Chirotope`
(`Chirotope`, `IsUniformChirotope`, `IsTope`, `IsCompleteCell`, `numCompleteCells`).
A rank-`r` uniform chirotope on `Fin n` is the oriented matroid of an arrangement of
`n` pseudohyperplanes in general position in `ℙ^{r-1}`. Setting `r = d + 1`, the
complete cells of the arrangement are the complete cells of the chirotope (topes all
of whose single-coordinate flips are again topes), counted up to antipode as cells in
`ℙ^d`, so Roudneff's conjecture is an upper bound on `numCompleteCells` of a uniform
chirotope.

*References:*
- [HKMS24] R. Hernández-Ortiz, K. Knauer, L. P. Montejano, and M. Scheucher,
  *Roudneff's conjecture in dimension 4*, Experimental Mathematics (2024),
  [doi:10.1080/10586458.2024.2334379](https://doi.org/10.1080/10586458.2024.2334379).
  Open-access version:
  [arXiv:2303.14212](https://arxiv.org/abs/2303.14212). States and studies
  Conjecture 1.1 for pseudohyperplane arrangements / oriented matroids.
- [Rou91] J.-P. Roudneff, *Cells with many facets in arrangements of hyperplanes*,
  Discrete Mathematics 98(3) (1991), 185–191. The original conjecture.
- [BLSWZ99] A. Björner, M. Las Vergnas, B. Sturmfels, N. White, and G. M. Ziegler,
  *Oriented Matroids*, Encyclopedia of Mathematics and its Applications 46,
  Cambridge University Press, 2nd ed., 1999. Source of the chirotope axioms.
-/

open Finset OrientedMatroid

namespace Roudneff

variable {r n : ℕ}

/--
**The Roudneff conjecture (Conjecture 1.1 of arXiv:2303.14212).** For every
dimension `d ≥ 2` and every `n ≥ 2d + 1`, an arrangement of `n` pseudohyperplanes
in general position in `ℙ^d` — equivalently, a uniform chirotope of rank `r = d+1`
on `Fin n` — has at most `∑_{i=0}^{d-2} binomial(n-1, i)` complete cells (topes all
of whose single-coordinate flips are again topes, counted up to antipode). The sum
`i = 0, …, d-2` is `Finset.range (d - 1)`.
-/
@[category research open, AMS 52 5]
theorem roudneff (d n : ℕ) (hd : 2 ≤ d) (hn : 2 * d + 1 ≤ n)
    (χ : Chirotope (d + 1) n) (hχ : IsUniformChirotope (d + 1) n χ) :
    numCompleteCells χ ≤ ∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i := by
  sorry

namespace variants

/--
**The Roudneff bound is tight.** For every `d ≥ 2` and `n ≥ 2d + 1` the bound
`∑_{i=0}^{d-2} binomial(n-1, i)` is attained: there is a uniform chirotope of rank
`d + 1` on `Fin n` (the *cyclic* / alternating oriented matroid, realized by the
cyclic hyperplane arrangement) whose number of complete cells equals the bound.
Hence the conjectured inequality cannot be improved.
-/
@[category research solved, AMS 52 5]
theorem roudneff_tight (d n : ℕ) (hd : 2 ≤ d) (hn : 2 * d + 1 ≤ n) :
    ∃ χ : Chirotope (d + 1) n, IsUniformChirotope (d + 1) n χ ∧
      numCompleteCells χ = ∑ i ∈ Finset.range (d - 1), Nat.choose (n - 1) i := by
  sorry

/--
**The planar case `d = 2`.** The `d = 2` instance of `roudneff`: for a uniform
chirotope of rank `3` on `Fin n` with `n ≥ 5` (an arrangement of `n` pseudolines
in the projective plane), the conjectured bound is
`∑_{i=0}^{0} binomial(n-1, i) = binomial(n-1, 0) = 1`, i.e.
`Finset.range (2 - 1) = Finset.range 1`: at most one complete cell in `ℙ^2`. This
does *not* contradict the fact that a rank-`3` arrangement has at least `n`
simplicial cells (mutations), because a complete cell is a different object from a
simplicial cell.
-/
@[category research open, AMS 52 5]
theorem roudneff_dim_two (n : ℕ) (hn : 5 ≤ n)
    (χ : Chirotope 3 n) (hχ : IsUniformChirotope 3 n χ) :
    numCompleteCells χ ≤ ∑ i ∈ Finset.range 1, Nat.choose (n - 1) i := by
  sorry

end variants

end Roudneff
