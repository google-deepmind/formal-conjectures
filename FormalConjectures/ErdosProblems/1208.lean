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

module

public import FormalConjecturesUtil

/-!
# Erdős Problem 1208

*References:*
- [erdosproblems.com/1208](https://www.erdosproblems.com/1208)
- [Er57b] Erdős, P., Néhány geometriai problémáról (On some geometrical problems, in Hungarian),
  Mat. Lapok 8 (1957), 86-92.
- [Er80] Erdős, P., A survey of problems in combinatorial number theory. Ann. Discrete Math.
  6 (1980), 89-115, p.110.
- [Th95] Thiele, T., Geometric selection problems and hypergraphs, PhD thesis, FU Berlin, 1995.
- [Ch13] Charalambides, M., A note on distinct distance subsets, J. Geom. 104 (2013), 439-442.
- [CFGHUZ15] Conlon, D., Fox, J., Gasarch, W., Harris, D. G., Ulrich, D. and Zbarsky, S.,
  [Distinct volume subsets](https://www.its.caltech.edu/~dconlon/distinctvol.pdf),
  SIAM J. Discrete Math. 29 (2015), no. 1, 472-480, Proposition 1.1.
- [CFR26] Clemen, F. C., Führer, J. and Roche-Newton, O., Geometric Sidon problems,
  [arXiv:2606.05841v1](https://arxiv.org/abs/2606.05841v1) (2026), Theorem 1.
- [LPZ26] Lee, S., Pohoata, C. and Zhu, D. G., The Minkowski grid has robustly many
  repeated distances, [arXiv:2607.05374v1](https://arxiv.org/abs/2607.05374v1) (2026),
  Corollary 3.
-/

@[expose] public section

open Filter
open scoped Asymptotics

namespace Erdos1208

/-- A finite set has distinct distances if equal distances between pairs of distinct points
determine the same unordered pair. -/
def HasDistinctDistances {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  PairwiseDistinctDistances (S : Set (EuclideanSpace ℝ (Fin d)))

/-- Largest cardinality of a distinct-distance subset of $P$. -/
noncomputable def maxDistinctDistanceSubset {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  sSup {m | ∃ S ⊆ P, HasDistinctDistances S ∧ S.card = m}

/-- Minimum, over all $n$-point sets in $\mathbb{R}^d$, of the largest cardinality of a
distinct-distance subset. -/
noncomputable def F (d n : ℕ) : ℕ :=
  sInf {m | ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧ maxDistinctDistanceSubset P = m}

@[category test, AMS 52]
theorem erdos_1208.test.empty {d : ℕ} :
    HasDistinctDistances (∅ : Finset (EuclideanSpace ℝ (Fin d))) := by
  intro p hp
  simp at hp

def erdos_1208.answer : ℕ → ℕ → ℝ := by
  sorry

/--
**Erdős Problem 1208.** [Er57b, Er80]

For $d \geq 2$ let $F_d(n)$ be minimal such that every set of $n$ points in $\mathbb{R}^d$ contains
a set of $F_d(n)$ points with distinct distances. Estimate $F_d(n)$ for fixed $d$ as $n \to \infty$.

The estimate is requested up to multiplicative constants depending on $d$, without imposing
a power-law form on the answer. The planar candidate $F_2(n) = n^{1/2-o(1)}$ was disproved
by Lee, Pohoata and Zhu [LPZ26, Corollary 3].
-/
@[category research open, question value, AMS 52]
theorem erdos_1208 :
    ∀ d : ℕ, 2 ≤ d →
      (fun n => (F d n : ℝ)) =Θ[atTop] erdos_1208.answer d := by
  sorry

/--
Is $F_2(n) = n^{1/2-o(1)}$, as asked in [CFGHUZ15]?
Lee, Pohoata and Zhu [LPZ26, Corollary 3] answered this question negatively.
This does not settle the problem of estimating $F_d(n)$.
-/
@[category research solved, question, AMS 52]
theorem erdos_1208.variants.planar_exponent :
    ¬ ∃ o : ℕ → ℝ, o =o[atTop] (fun _ => (1 : ℝ)) ∧
      (fun n => (F 2 n : ℝ)) =ᶠ[atTop] fun n => (n : ℝ) ^ ((1 : ℝ) / 2 - o n) := by
  sorry

/--
The integer grid gives $F_d(n) \ll n^{1/d}$ for $d \geq 2$
[erdosproblems.com/1208].
-/
@[category research solved, AMS 52]
theorem erdos_1208.upper_bound (d : ℕ) (hd : 2 ≤ d) :
    (fun n => (F d n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((1 : ℝ) / (d : ℝ)) := by
  sorry

/--
Conlon, Fox, Gasarch, Harris, Ulrich and Zbarsky [CFGHUZ15, Proposition 1.1] proved
$F_d(n) \gg_d n^{1/(3d-3)}(\log n)^{1/3-2/(3d-3)}$ for $d \geq 2$.
At $d=2$ this is $F_2(n) \gg n^{1/3}/(\log n)^{1/3}$.
-/
@[category research solved, AMS 52]
theorem erdos_1208.variants.lower_bound_cfghuz (d : ℕ) (hd : 2 ≤ d) :
    (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (3 * (d : ℝ) - 3)) *
      (Real.log (n : ℝ)) ^ ((1 : ℝ) / 3 - 2 / (3 * (d : ℝ) - 3))) =O[atTop]
      fun n => (F d n : ℝ) := by
  sorry

/--
The bound $F_d(n) \gg_d n^{1/(3d-3)}$ holds for every $d \geq 2$.
For $d \geq 3$ it follows from [CFGHUZ15, Proposition 1.1], since the logarithmic exponent
is nonnegative. For $d=2$ it is the improvement of Clemen, Führer and Roche-Newton
[CFR26, Theorem 1].
-/
@[category research solved, AMS 52]
theorem erdos_1208.lower_bound (d : ℕ) (hd : 2 ≤ d) :
    (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (3 * (d : ℝ) - 3))) =O[atTop] fun n => (F d n : ℝ) := by
  sorry

/--
Clemen, Führer and Roche-Newton [CFR26, Theorem 1] proved $F_2(n) \gg n^{1/3}$.
-/
@[category research solved, AMS 52]
theorem erdos_1208.lower_bound_plane :
    (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 3)) =O[atTop] fun n => (F 2 n : ℝ) := by
  sorry

/--
The planar grid construction gives
$F_2(n) \ll n^{1/2} / (\log n)^{1/4}$ [erdosproblems.com/1208].
-/
@[category research solved, AMS 52]
theorem erdos_1208.upper_bound_plane :
    (fun n => (F 2 n : ℝ)) =O[atTop]
      fun n => (n : ℝ) ^ ((1 : ℝ) / 2) / (Real.log (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  sorry

/--
Lee, Pohoata and Zhu [LPZ26, Corollary 3] proved that there is an absolute constant
$\delta>0$ such that $F_2(n) \ll n^{1/2-\delta}$.
-/
@[category research solved, AMS 52]
theorem erdos_1208.variants.upper_bound_plane_lpz :
    ∃ δ : ℝ, 0 < δ ∧
      (fun n => (F 2 n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((1 : ℝ) / 2 - δ) := by
  sorry

end Erdos1208
