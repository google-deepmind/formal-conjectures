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
# Erdős Problem 1089

*References:*
- [erdosproblems.com/1089](https://www.erdosproblems.com/1089)
- [BBS83] Bannai, Eiichi and Bannai, Etsuko and Stanton, Dennis, *An upper bound for the
  cardinality of an $s$-distance subset in real Euclidean space. II*. Combinatorica (1983),
  147-152.
- [Cr62] Croft, H. T., *$9$-point and $7$-point configurations in $3$-space*. Proc. London Math.
  Soc. (3) (1962), 400-424.
- [Er75f] Erdős, Paul, *On some problems of elementary and combinatorial geometry*. Ann. Mat. Pura
  Appl. (4) (1975), 99-108.
- [Fe26] T. Feng et al, *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the
  Erdős Problems*. arXiv:2601.22401 (2026).
-/

open Filter Topology

namespace Erdos1089

/--
$g_d(n)$ is the least number such that every collection of $g_d(n)$ points in $\mathbb{R}^d$
determines at least $n$ distinct distances.
-/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = m → n ≤ distinctDistances P}

@[category test, AMS 52]
theorem distinctDistances_empty (d : ℕ) :
    distinctDistances (∅ : Finset (EuclideanSpace ℝ (Fin d))) = 0 := by
  simp [distinctDistances, distanceSet]

@[category test, AMS 52]
theorem g_zero (d : ℕ) : g d 0 = 0 := by
  refine Nat.eq_zero_of_le_zero (csInf_le (OrderBot.bddBelow _) ?_)
  intro P _
  exact Nat.zero_le _

/--
Let $g_d(n)$ be minimal such that every collection of $g_d(n)$ points in $\mathbb{R}^d$ determines
at least $n$ many distinct distances. Estimate $g_d(n)$. In particular, does
$$\lim_{d\to \infty}\frac{g_d(n)}{d^{n-1}}$$
exist?

A question of Kelly. For $n\geq 2$ the limit exists and equals $1/(n-1)!$.
-/
@[category research solved, AMS 52, formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/33a6b9a285cb64ac276ce4d0b3a4111b82c972b6/src/latest/ErdosProblems/Erdos1089.lean"]
theorem erdos_1089 :
    answer(True) ↔
      ∀ n ≥ 2, ∃ L : ℝ,
        Tendsto (fun d : ℕ ↦ (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop (𝓝 L) := by
  sorry

/--
For $n\geq 2$,
$$\lim_{d\to \infty}\frac{g_d(n)}{d^{n-1}}=\frac{1}{(n-1)!}.$$
-/
@[category research solved, AMS 52, formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/33a6b9a285cb64ac276ce4d0b3a4111b82c972b6/src/latest/ErdosProblems/Erdos1089.lean"]
theorem erdos_1089.variants.limit (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun d : ℕ ↦ (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
      (𝓝 ((1 : ℝ) / (n - 1).factorial)) := by
  sorry

/--
Aletheia [Fe26] proved that, for $n\geq 2$,
$$\binom{d+1}{n-1}+1\leq g_d(n).$$
This generalises the construction in [502].
-/
@[category research solved, AMS 52, formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/33a6b9a285cb64ac276ce4d0b3a4111b82c972b6/src/latest/ErdosProblems/Erdos1089.lean"]
theorem erdos_1089.variants.lower_bound (d n : ℕ) (hn : 2 ≤ n) :
    (d + 1).choose (n - 1) + 1 ≤ g d n := by
  sorry

/--
Bannai, Bannai, and Stanton [BBS83] proved that, for $n\geq 2$,
$$g_d(n) \leq \binom{d+n-1}{n-1}+1.$$
-/
@[category research solved, AMS 52, formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/33a6b9a285cb64ac276ce4d0b3a4111b82c972b6/src/latest/ErdosProblems/Erdos1089.lean"]
theorem erdos_1089.variants.upper_bound (d n : ℕ) (hn : 2 ≤ n) :
    g d n ≤ (d + n - 1).choose (n - 1) + 1 := by
  sorry

/-- It is trivial that $g_1(3)=4$. -/
@[category textbook, AMS 52]
theorem erdos_1089.variants.g_one_three : g 1 3 = 4 := by
  sorry

/-- It is easy to see that $g_2(3)=6$. -/
@[category textbook, AMS 52]
theorem erdos_1089.variants.g_two_three : g 2 3 = 6 := by
  sorry

/-- Croft [Cr62] proved $g_3(3)=7$. -/
@[category research solved, AMS 52]
theorem erdos_1089.variants.g_three_three : g 3 3 = 7 := by
  sorry

/--
The vertices of a $d$-dimensional cube demonstrate that
$$g_d(d+1)>2^d.$$
-/
@[category research solved, AMS 52]
theorem erdos_1089.variants.cube (d : ℕ) : 2 ^ d < g d (d + 1) := by
  sorry

end Erdos1089
