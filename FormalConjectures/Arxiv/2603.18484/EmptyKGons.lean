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
# Number of `k`-holes in planar point sets

A `k`-hole of a finite planar point set `P` (in general position, i.e. no three
points on a line) is a convex `k`-gon with vertices in `P` whose interior
contains no point of `P`. It is the *empty* variant of the Erdős–Szekeres `k`-gon
problem (the Happy Ending problem, `FormalConjectures.Wikipedia.HappyEndingProblem`
and `FormalConjectures.ErdosProblems.«107»`). Let `h_k(n)` be the minimum number
of `k`-holes over all `n`-point sets in general position (`minKHoles` in
`FormalConjecturesForMathlib.Geometry.2d`).

It is known that `h_k(n) = Θ(n²)` for `k ∈ {3, 4, 5}` in the sense that both an
`Ω(·)` and an `O(n²)` bound hold — except that for `k = 5` the quadratic lower
bound is *not* known: the best known lower bounds are super-linear but
sub-quadratic. The three open conjectures below concern the leading constant of
the quadratic term.

- For `k = 3` and `k = 4` quadratic growth is established; only the value of the
  leading constant is open.
- For `k = 5` even `h₅(n) = Ω(n²)` is open. The current record lower bound is
  `Ω(n^{20/11})`, proved in the paper this folder is named after.

*References:*
- [ASP26] O. Astudillo-Marbán and O. Solé-Pi, *There are many 5-holes*,
  arXiv:2603.18484 (2026). The `Ω(n^{20/11})` bound, and a survey of the
  conjectures below (their Problems 1 and 2).
- [BK00] I. Bárány and G. Károlyi, *Problems and results around the
  Erdős–Szekeres convex polygon theorem*, Japanese Conference on Discrete and
  Computational Geometry (2000), 91–105.
  [doi:10.1007/3-540-47738-1_7](https://doi.org/10.1007/3-540-47738-1_7).
  Source of the 3-hole conjecture (Problem 1).
- [BMP05] P. Brass, W. Moser, and J. Pach, *Research Problems in Discrete
  Geometry*, Springer (2005), Chapter 8.4, Problem 5.
  [doi:10.1007/0-387-29929-7](https://doi.org/10.1007/0-387-29929-7).
- [Ai09] O. Aichholzer, *[Empty] [colored] k-gons. Recent results on some
  Erdős–Szekeres type problems*, Proc. XIII Encuentros de Geometría
  Computacional, Zaragoza (2009), 43–52.
- [ABHKPSVV20] O. Aichholzer, M. Balko, T. Hackl, J. Kynčl, I. Parada, M. Scheucher,
  P. Valtr, and B. Vogtenhuber, *A superlinear lower bound on the number of
  5-holes*, J. Combin. Theory Ser. A 173 (2020), 105236.
  [doi:10.1016/j.jcta.2020.105236](https://doi.org/10.1016/j.jcta.2020.105236),
  arXiv:1703.05253. The `Ω(n · log^{4/5} n)` bound.
- [Deh87] K. Dehnhardt, *Leere konvexe Vielecke in ebenen Punktmengen*, PhD thesis,
  TU Braunschweig, 1987 (in German). First study of the numbers `h_3`, `h_4`, `h_5`.
- [Sch18] M. Scheucher, *Two disjoint 5-holes in point sets*,
  [arXiv:1807.10848](https://arxiv.org/abs/1807.10848) (2018). SAT encoding for
  hole-counting searches.
- OEIS sequences of minimum k-hole counts: [A063541](https://oeis.org/A063541)
  (3-holes), [A063542](https://oeis.org/A063542) (4-holes),
  [A276096](https://oeis.org/A276096) (5-holes).
- [Wikipedia: Empty triangle](https://en.wikipedia.org/wiki/Empty_triangle)
-/

open EuclideanGeometry

namespace EmptyKGons

/-!
## The three open conjectures on the leading constant

Each is phrased, following [ASP26] and [BMP05], as the existence of a constant
improving on the trivial quadratic leading term. `minKHoles k n` is `h_k(n)`.

The three problems are tightly linked. Writing `c_k` for the leading constant of
`h_k(n)` (its `n²`-coefficient, `leadingConst k` below), Pinchasi, Radoičić and
Sharir proved `c₅ ≥ c₃ - 1` and `c₄ ≥ c₃ - 1/2`. In particular, resolving the
3-hole problem in the affirmative (`c₃ > 1`) resolves all three at once: it forces
`c₄ > 1/2` and `c₅ > 0` (so `h₅(n) = Ω(n²)`). All three are widely believed to
hold. See `variants` below.
-/

/-- The leading constant `c_k` of `h_k(n)`: the `n²`-coefficient of the number of
`k`-holes, defined as `liminf_{n→∞} h_k(n) / n²`. -/
noncomputable def leadingConst (k : ℕ) : ℝ :=
  Filter.liminf (fun n => (minKHoles k n : ℝ) / (n : ℝ) ^ 2) Filter.atTop

/--
**Problem 1 (Bárány–Károlyi).** Is there an absolute constant `ε > 0` such that
`h₃(n) ≥ (1 + ε) n²` for every sufficiently large `n`?

The known lower bound is `h₃(n) ≥ n² - O(n)` (so `c₃ ≥ 1`); the question is
whether the leading constant can be pushed above `1`.
-/
@[category research open, AMS 52]
theorem h3_leading_constant :
    answer(sorry) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in Filter.atTop,
        (1 + ε) * (n : ℝ) ^ 2 ≤ minKHoles 3 n := by
  sorry

/--
**Problem 2, part 1.** Is there a constant `ε₁ > 0` such that
`h₄(n) ≥ (1/2 + ε₁) n²` for every sufficiently large `n`?

The known lower bound is `h₄(n) ≥ (1/2) n² - o(n²)` (so `c₄ ≥ 1/2`); the question
is whether the leading constant exceeds `1/2`.
-/
@[category research open, AMS 52]
theorem h4_leading_constant :
    answer(sorry) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in Filter.atTop,
        (1 / 2 + ε) * (n : ℝ) ^ 2 ≤ minKHoles 4 n := by
  sorry

/--
**Problem 2, part 2.** Is there a constant `ε₂ > 0` such that
`h₅(n) ≥ ε₂ n²` for every sufficiently large `n`? Equivalently: is
`h₅(n) = Ω(n²)`?

Unlike `k = 3, 4`, no quadratic lower bound is known for `k = 5`; only
super-linear bounds (see `variants` below).
-/
@[category research open, AMS 52]
theorem h5_quadratic :
    answer(sorry) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in Filter.atTop,
        ε * (n : ℝ) ^ 2 ≤ minKHoles 5 n := by
  sorry

namespace variants

/--
Matching quadratic upper bounds: for `k ∈ {3, 4, 5}` there are `n`-point sets in
general position with only `O(n²)` `k`-holes (Bárány–Valtr constructions). Hence
the conjectures above are about the leading constant of a genuinely quadratic
quantity.
-/
@[category research solved, AMS 52]
theorem quadratic_upper_bound (k : ℕ) (hk : k ∈ ({3, 4, 5} : Set ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in Filter.atTop,
      (minKHoles k n : ℝ) ≤ C * (n : ℝ) ^ 2 := by
  sorry

/--
**Pinchasi–Radoičić–Sharir relation, 4-holes vs 3-holes.** The leading constants
satisfy `c₄ ≥ c₃ - 1/2`. Hence `c₃ > 1` implies `c₄ > 1/2`.

[PRS06] R. Pinchasi, R. Radoičić, and M. Sharir, *On empty convex polygons in a
planar point set*, J. Combin. Theory Ser. A 113(3) (2006), 385–419, p. 4.
[doi:10.1016/j.jcta.2005.03.007](https://doi.org/10.1016/j.jcta.2005.03.007).
-/
@[category research solved, AMS 52]
theorem c4_ge_c3_sub_half : leadingConst 4 ≥ leadingConst 3 - 1 / 2 := by
  sorry

/--
**Pinchasi–Radoičić–Sharir relation, 5-holes vs 3-holes.** The leading constants
satisfy `c₅ ≥ c₃ - 1`. Hence `c₃ > 1` implies `c₅ > 0`, i.e. `h₅(n) = Ω(n²)`
(Valtr's implication). [PRS06], p. 4.
-/
@[category research solved, AMS 52]
theorem c5_ge_c3_sub_one : leadingConst 5 ≥ leadingConst 3 - 1 := by
  sorry

/--
[ABHKPSVV20] proved the first super-linear lower bound on the number of 5-holes:
`h₅(n) = Ω(n · (log n)^{4/5})`.
-/
@[category research solved, AMS 52]
theorem h5_superlinear :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop,
      c * (n : ℝ) * Real.log n ^ (4 / 5 : ℝ) ≤ minKHoles 5 n := by
  sorry

/--
[ASP26] improved the 5-hole lower bound to `h₅(n) = Ω(n^{20/11})`, the current
record. This is the paper this folder is named after.
-/
@[category research solved, AMS 52]
theorem h5_astudillo_sole :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop,
      c * (n : ℝ) ^ (20 / 11 : ℝ) ≤ minKHoles 5 n := by
  sorry

end variants

end EmptyKGons
