/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 51

*Reference:* [erdosproblems.com/51](https://www.erdosproblems.com/51)
-/

namespace Erdos51

/--
Is there an infinite set A ⊆ ℕ such that for every a ∈ A,
there is an integer n such that ϕ(n)=a, and
yet if nₐ is the smallest such integer, then nₐ/a → ∞ as a → ∞?
-/
@[category research open, AMS 11]
theorem erdos_51 :
    ∃ A : Set ℕ, ∃ n : A → ℕ,
      A.Infinite ∧
      ∀ a : A, IsLeast (Nat.totient ⁻¹' {(a : ℕ)}) (n a) ∧
      Filter.Tendsto (fun a : A => (n a : ℝ) / (a : ℝ)) Filter.atTop Filter.atTop
    ↔ answer(sorry) := by
  sorry

/-
The remarks from the erdosproblems site are the same as those in
[erdosproblems.com/694](https://www.erdosproblems.com/694).
-/

end Erdos51
