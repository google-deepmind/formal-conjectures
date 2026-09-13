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
# Erdős Problem 941

*Reference:* [erdosproblems.com/941](https://www.erdosproblems.com/941)
-/

open Filter

namespace Erdos941

/-- A number is powerful if $p\mid n$ implies $p^2\mid n$. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Are all large integers the sum of at most three powerful numbers (i.e. if $p\mid n$ then
$p^2\mid n$)?
-/
@[category research open, AMS 11]
theorem erdos_941 :
    answer(sorry) ↔
      ∀ᶠ n : ℕ in atTop,
        ∃ a b c : ℕ, Powerful a ∧ Powerful b ∧ Powerful c ∧ n = a + b + c := by
  sorry

end Erdos941
