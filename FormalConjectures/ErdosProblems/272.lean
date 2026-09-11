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
# Erdős Problem 272

*Reference:* [erdosproblems.com/272](https://www.erdosproblems.com/272)
-/

open Filter Asymptotics Finset

namespace Erdos272

/-- Let $N \in\mathbb{N}$. We say that $\{A_1, ..., A_t\}\subseteq
\mathcal{P}(\{1, \dots, N\})$ is an arithmetic intersection set if
$A_i \cap A_j$ is a non-empty arithmetic progression for each $i \neq j$.
-/
def IsArithInterSet (N : ℕ) (A : Finset (Finset ℕ)) : Prop :=
  A ⊆ (Finset.Icc 1 N).powerset ∧
    (SetLike.coe A).Pairwise fun S T ↦ ∃ l > 0, (SetLike.coe (S ∩ T)).IsAPOfLength l

/-- For each $N > 0$, let $t$ be the largest size of an arithmetic
intersection set. -/
noncomputable def maxArithInterCard (N : ℕ) : ℕ :=
  sSup {#A | (A : _) (_ : IsArithInterSet N A)}

/--
Simonovits and Sós have shown that $t\ll N^2$.
-/
@[category research solved, AMS 5]
theorem erdos_272.variants.isBigO_sq :
    (fun N ↦ (maxArithInterCard N : ℝ)) =O[atTop] fun N ↦ (N : ℝ) ^ 2 := by
  sorry

/-- Szabo showed that the maximal $t$ is equal to
$$
  \frac{N^2}{2} + O(N^{5/3}\log^3N).
$$
-/
@[category research solved, AMS 5]
theorem erdos_272.variants.szabo :
    (fun N ↦ (maxArithInterCard N - N ^ 2 / 2 : ℝ)) =O[atTop]
      fun N : ℕ ↦ N ^ ((5 : ℝ) /  3) * (Real.log N) ^ 3 := by
  sorry

/--
Let $N\geq 1$. What is the largest $t$ such that there are
$A_1,\ldots,A_t\subseteq \{1,\ldots,N\}$ with $A_i\cap A_j$ a non-empty
arithmetic progression for all $i\neq j$? Szabó's error estimate above implies the asymptotic
$t \sim N^2/2$.
-/
@[category research solved, AMS 5]
theorem erdos_272 :
    (fun N ↦ (maxArithInterCard N : ℝ)) ~[atTop]
      answer(fun N : ℕ ↦ (N : ℝ) ^ 2 / 2) := by
  rw [Asymptotics.IsEquivalent]
  apply erdos_272.variants.szabo.trans_isLittleO
  have hlog : (fun x : ℝ ↦ Real.log x ^ (3 : ℝ)) =o[atTop]
      (fun x : ℝ ↦ x ^ ((1 : ℝ) / 3)) :=
    isLittleO_log_rpow_rpow_atTop 3 (by norm_num)
  have hmul := (isBigO_refl (fun x : ℝ ↦ x ^ ((5 : ℝ) / 3)) atTop).mul_isLittleO hlog
  have hnat := hmul.comp_tendsto tendsto_natCast_atTop_atTop
  have hbase : (fun N : ℕ ↦ (N : ℝ) ^ ((5 : ℝ) / 3) * Real.log N ^ (3 : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ) ^ (2 : ℝ)) := by
    apply (hnat.congr_left fun _ => rfl).congr_right
    intro N
    simp only [Function.comp_apply]
    rw [← Real.rpow_add' (Nat.cast_nonneg N) (by norm_num : (5 / 3 : ℝ) + 1 / 3 ≠ 0)]
    norm_num
  have hfinal := hbase.const_mul_right (by norm_num : (1 / 2 : ℝ) ≠ 0)
  simpa [div_eq_mul_inv, mul_comm] using hfinal

/-- Szabo asks whether the maximal $t$ is given by
$$
  \frac{N^2}{2} + O(N)
$$
-/
@[category research open, AMS 5]
theorem erdos_272.variants.szabo_strong :
    (fun N ↦ (maxArithInterCard N - N ^ 2 / 2 : ℝ)) =O[atTop] fun N : ℕ ↦ (N : ℝ) := by
  sorry

end Erdos272
