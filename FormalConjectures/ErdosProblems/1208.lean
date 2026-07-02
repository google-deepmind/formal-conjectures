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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1208

*References:*
- [erdosproblems.com/1208](https://www.erdosproblems.com/1208)
- [Er57b] Erdős, P., Néhány geometriai problémáról (On some geometrical problems, in Hungarian),
  Mat. Lapok 8 (1957), 86-92.
- [Er80] Erdős, P., A survey of problems in combinatorial number theory. Ann. Discrete Math.
  (1980), 89-115, p.110.
- [Th95] Thiele, T., Geometric selection problems and hypergraphs, PhD thesis, FU Berlin, 1995.
- [Ch13] Charalambides, M., A note on distinct distance subsets, J. Geom. 104 (2013), 439-442.
- [CFGHUZ15] Conlon, D., Fox, J., Gasarch, W., Harris, D. G., Ulrich, D. and Zbarsky, S.,
  Distinct volume subsets, SIAM J. Discrete Math. 29 (2015), 472-480.
- [CFR26] Clemen, F. C., Führer, J. and Roche-Newton, O., Geometric Sidon problems,
  arXiv:2606.05841 (2026).

For $d \geq 2$ let $F_d(n)$ be minimal such that every set of $n$ points in $\mathbb{R}^d$ contains
a set of $F_d(n)$ points with distinct distances. Estimate $F_d(n)$ for fixed $d$ as $n \to \infty$.

The example of the integer grid shows $F_d(n) \ll n^{1/d}$. Thiele [Th95] proved
$F_d(n) \gg n^{1/(3d-2)}$ for $d \geq 3$, improved by Conlon, Fox, Gasarch, Harris, Ulrich and
Zbarsky [CFGHUZ15] to $F_d(n) \gg_d n^{1/(3d-3)}(\log n)^{1/3 - 2/(3d-3)}$. In the plane the lower
bound was proved by Charalambides [Ch13] (as $n^{1/3}/(\log n)^{1/3}$) and improved by Clemen,
Führer and Roche-Newton [CFR26] to $F_2(n) \gg n^{1/3}$, so that
$n^{1/3} \ll F_2(n) \ll n^{1/2}/(\log n)^{1/4}$. The order of magnitude is open for every $d \geq 2$;
the conjecture is $F_d(n) = n^{1/d - o(1)}$.
-/

open Filter
open scoped Asymptotics

namespace Erdos1208

/-- A finite set of points has *distinct distances* if all of its pairwise distances are distinct:
whenever two pairs `{p, q}` and `{r, s}` of distinct points of `S` realise the same distance, the
two pairs coincide. -/
def HasDistinctDistances {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, ∀ s ∈ S, p ≠ q → r ≠ s → dist p q = dist r s →
    (p = r ∧ q = s) ∨ (p = s ∧ q = r)

/-- The largest size of a distinct-distance subset of a finite point set `P` in `ℝ^d`. -/
noncomputable def maxDistinctDistanceSubset {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  sSup {m | ∃ S ⊆ P, HasDistinctDistances S ∧ S.card = m}

/-- `F d n` is the largest size of a distinct-distance subset that is *guaranteed* in every
`n`-point set in `ℝ^d`: the minimum, over all `n`-point sets `P`, of `maxDistinctDistanceSubset P`.
Equivalently, every `n`-point set contains `F d n` points with pairwise distinct distances, and
some `n`-point set contains no larger such subset. -/
noncomputable def F (d n : ℕ) : ℕ :=
  sInf {m | ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧ maxDistinctDistanceSubset P = m}

@[category test, AMS 52]
theorem erdos_1208.test.empty {d : ℕ} :
    HasDistinctDistances (∅ : Finset (EuclideanSpace ℝ (Fin d))) := by
  intro p hp
  simp at hp

/--
**Erdős Problem 1208.** For each fixed `d ≥ 2`, estimate `F d n` as `n → ∞`. The conjectured
answer is `F_d(n) = n^{1/d - o(1)}`, i.e. the integer-grid upper bound is essentially tight. This
is open for every `d ≥ 2`; in the plane it is the question whether `F_2(n) = n^{1/2 - o(1)}`.
-/
@[category research open, AMS 52]
theorem erdos_1208 (d : ℕ) (hd : 2 ≤ d) :
    ∃ o : ℕ → ℝ, o =o[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n => (F d n : ℝ)) =ᶠ[atTop] fun n => (n : ℝ) ^ ((1 : ℝ) / (d : ℝ) - o n) := by
  sorry

/--
The integer grid `{1, …, n^{1/d}}^d` shows `F_d(n) ≪ n^{1/d}` for `d ≥ 2`.
-/
@[category research solved, AMS 52]
theorem erdos_1208.upper_bound (d : ℕ) (hd : 2 ≤ d) :
    (fun n => (F d n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((1 : ℝ) / (d : ℝ)) := by
  sorry

/--
Conlon, Fox, Gasarch, Harris, Ulrich and Zbarsky [CFGHUZ15] proved
`F_d(n) ≫_d n^{1/(3d-3)}` for `d ≥ 2` (with an additional logarithmic factor), improving
Thiele's `n^{1/(3d-2)}` for `d ≥ 3`.
-/
@[category research solved, AMS 52]
theorem erdos_1208.lower_bound (d : ℕ) (hd : 2 ≤ d) :
    (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (3 * (d : ℝ) - 3))) =O[atTop] fun n => (F d n : ℝ) := by
  sorry

/--
In the plane, Clemen, Führer and Roche-Newton [CFR26] proved `F_2(n) ≫ n^{1/3}`, removing the
`(log n)^{1/3}` factor from the earlier bound of Charalambides [Ch13].
-/
@[category research solved, AMS 52]
theorem erdos_1208.lower_bound_plane :
    (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 3)) =O[atTop] fun n => (F 2 n : ℝ) := by
  sorry

/--
The upper bound for the plane: the `√n × √n` grid determines `≪ n / √(log n)` distinct distances,
whence `F_2(n) ≪ n^{1/2} / (log n)^{1/4}`.
-/
@[category research solved, AMS 52]
theorem erdos_1208.upper_bound_plane :
    (fun n => (F 2 n : ℝ)) =O[atTop]
      fun n => (n : ℝ) ^ ((1 : ℝ) / 2) / (Real.log (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  sorry

end Erdos1208
