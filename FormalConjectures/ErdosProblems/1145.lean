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
import FormalConjectures.ErdosProblems.«28»

/-!
# Erdős Problem 1145

*References:*
- [erdosproblems.com/1145](https://www.erdosproblems.com/1145)
- [erdosproblems.com/28](https://www.erdosproblems.com/28)
- [erdosproblems.com/331](https://www.erdosproblems.com/331)
-/

open Set Filter Pointwise Topology AdditiveCombinatorics

namespace Erdos1145

/-- Ordered representations of `n` as `a + b` with `a ∈ A` and `b ∈ B`.
This is the two-set analogue of `sumRep`. -/
noncomputable def sumRepAB (A B : Set ℕ) : ℕ → ℕ := (𝟙_A ∗ 𝟙_B : ℕ → ℕ)

/-- Integers whose binary expansion is supported only on even bit positions. -/
def evenBinaryDigits : Set ℕ := {n | ∀ k, n.testBit (2 * k + 1) = false}

/-- Integers whose binary expansion is supported only on odd bit positions. -/
def oddBinaryDigits : Set ℕ := {n | ∀ k, n.testBit (2 * k) = false}

/--
Let $A=\{1\leq a_1 < a_2 < \cdots\}$ and $B=\{1\leq b_1 < b_2 < \cdots\}$ be sets of integers
with $a_n/b_n\to 1$.

If $A+B$ contains all sufficiently large positive integers then is it true that
$$\limsup 1_A\ast 1_B(n)=\infty?$$

The enumerations $a_n$ and $b_n$ are the increasing enumerations of $A$ and $B$
(`Nat.nth`). The source writes $1\le a_1$; we work with `Set ℕ`, so `0` is allowed.
-/
def Erdos1145Prop : Prop :=
  ∀ ⦃A B : Set ℕ⦄ (_ : A.Infinite) (_ : B.Infinite),
    Tendsto (fun n ↦ (Nat.nth (· ∈ A) n : ℝ) / (Nat.nth (· ∈ B) n : ℝ)) atTop (𝓝 1) →
    (∀ᶠ n in atTop, n ∈ A + B) →
    limsup (fun n ↦ (sumRepAB A B n : ℕ∞)) atTop = ⊤

/--
Let $A=\{1\leq a_1 < a_2 < \cdots\}$ and $B=\{1\leq b_1 < b_2 < \cdots\}$ be sets of integers
with $a_n/b_n\to 1$.

If $A+B$ contains all sufficiently large positive integers then is it true that
$$\limsup 1_A\ast 1_B(n)=\infty?$$

A conjecture of Erdős and Sárközy. This is a stronger form of [erdosproblems.com/28].
See also [erdosproblems.com/331].
-/
@[category research open, AMS 11]
theorem erdos_1145 : answer(sorry) ↔ Erdos1145Prop := by
  sorry

/--
Some condition relating $A$ and $B$ is necessary: if $A$ is the set of integers with only
even binary digits and $B$ is the set of integers with only odd binary digits, then
$$1_A\ast 1_B(n)=1$$
for all $n$.
-/
@[category research solved, AMS 11]
theorem erdos_1145.variants.even_odd_binary_digits :
    (∀ n, sumRepAB evenBinaryDigits oddBinaryDigits n = 1) ∧
      evenBinaryDigits + oddBinaryDigits = univ := by
  sorry

/--
A stronger form of [erdosproblems.com/28].
-/
@[category test, AMS 11]
theorem erdos_1145.test_implies_erdos_28 : Erdos1145Prop → type_of% Erdos28.erdos_28 := by
  delta sumRep sumRepAB
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
