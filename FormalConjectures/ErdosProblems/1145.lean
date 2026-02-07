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
import FormalConjectures.ErdosProblems.«28»

/-!
# Erdős Problem 1145

*References:*
- [erdosproblems.com/28](https://www.erdosproblems.com/28)
- [erdosproblems.com/1145](https://www.erdosproblems.com/1145)
-/

open Set Filter Pointwise Topology AdditiveCombinatorics

namespace Erdos1145


def Erdos1145Prop : Prop :=
  ∀ ⦃A B : Set ℕ⦄ (_ : A.Infinite) (_ : B.Infinite),
    Tendsto (fun n ↦ (Nat.nth (· ∈ A) n : ℝ) / (Nat.nth (· ∈ B) n : ℝ)) atTop (𝓝 1) →
    (∀ᶠ n in atTop, n ∈ A + B) →
    limsup (fun n => ↑(((𝟙_A ∗ 𝟙_B) : ℕ → ℕ) n)) atTop = (⊤ : ℕ∞)

/--
Let $A=\{1\leq a_1 < a_2 < \cdots\}$ and $B=\{1\leq b_1 < b_2 < \cdots\}$ be sets of integers with
$a_n/b_n\to 1$.

If $A+B$ contains all sufficiently large positive integers then is it true that
$\limsup 1_A\ast 1_B(n)=\infty$?

A conjecture of Erdős and Sárközy.
-/
@[category research open, AMS 5]
theorem erdos_1145 : answer(sorry) ↔ Erdos1145Prop := by
  sorry

/--
A stronger form of [erdosproblems.com/28].
-/
@[category test, AMS 11]
theorem erdos_1145_implies_erdos_28 : Erdos1145Prop → type_of% Erdos28.erdos_28 := by
  delta sumRep
  intro h1145 s hs
  rcases hs.exists_le with ⟨m, hm⟩
  by_cases hfin : s.Finite
  · exact absurd hs (hfin.add hfin).infinite_compl
  · have hinf : s.Infinite := hfin
    refine h1145 hinf hinf ?_ ?_
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [div_self]
      exact mod_cast Nat.pos_iff_ne_zero.mp <|
        lt_of_lt_of_le hn (Nat.nth_strictMono hinf).le_apply
    · filter_upwards [Filter.eventually_gt_atTop m] with n hn
      by_contra hns
      exact not_le_of_gt hn (hm n hns)

end Erdos1145
