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
# Erdős Problem 1145

*References:*
- [erdosproblems.com/28](https://www.erdosproblems.com/28)
- [erdosproblems.com/1145](https://www.erdosproblems.com/1145)
-/

open Set Filter Pointwise Topology

namespace Erdos1145


/--
Let $A=\{1\leq a_1 < a_2 < \cdots\}$ and $B=\{1\leq b_1 < b_2 < \cdots\}$ be sets of integers with
$a_n/b_n\to 1$.

If $A+B$ contains all sufficiently large positive integers then is it true that
$\limsup 1_A\ast 1_B(n)=\infty$?

A conjecture of Erdős and Sárközy.

A stronger form of [erdosproblems.com/28].
-/
@[category research open, AMS 5]
theorem erdos_1145 :
  answer(sorry) ↔ ∀ ⦃A B : Set ℕ⦄ (hA : A.Infinite) (hB : B.Infinite),
    0 ∉ A →
    0 ∉ B →
    Tendsto (fun n ↦ (Nat.nth (· ∈ A) n : ℝ) / (Nat.nth (· ∈ B) n : ℝ)) atTop (𝓝 1) →
    (∀ᶠ n in atTop, n ∈ A + B) →
    limsup (fun n ↦ ({p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n}.ncard : ℕ∞)) atTop = ⊤ := by
  sorry

end Erdos1145
