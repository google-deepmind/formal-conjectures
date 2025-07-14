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
# Erdős Problem 689
*Reference:* [erdosproblems.com/689](https://www.erdosproblems.com/689)
-/

/--
Is there some choice of congruence class `a_p` for all primes `2 ≤ p ≤ n` such that every integer
in `[1,n]` satisfies at least two of the congruences `≡ a_p (mod p)`?
-/
@[category research open, AMS 11]
theorem erdos_689 :
    (∀ n ≥ 3, ∃ a : ℕ → ℕ, ∀ m ∈ Finset.Icc 1 n,
      2 ≤ (Finset.Icc 1 n |>.filter fun p => p.Prime ∧ a p ≡ m [MOD p]).card)
    ↔ answer(sorry) := by
  sorry
