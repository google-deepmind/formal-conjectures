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
# Erdős Problem 1081

*Reference:* [erdosproblems.com/1081](https://www.erdosproblems.com/1081)
-/

open Filter Asymptotics

namespace Erdos1081

/-- A number `m` is squarefull if `p ∣ m` implies `p^2 ∣ m` for every prime `p`. -/
def Squarefull (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

/-- `A(x)` counts the number of `n ≤ x` which are the sum of two squarefull numbers. -/
noncomputable def A (x : ℕ) : ℕ :=
  { n : ℕ | n ≤ x ∧ ∃ a b : ℕ, Squarefull a ∧ Squarefull b ∧ n = a + b }.ncard

/--
Let $A(x)$ count the number of $n\leq x$ which are the sum of two squarefull numbers (a number $m$
is squarefull if $p\mid m$ implies $p^2\mid m$). Is it true that
$$
A(x) \sim c \frac{x}{\sqrt{\log x}}
$$
for some $c>0$?
-/
@[category research open, AMS 11]
theorem erdos_1081 :
    answer(sorry) ↔
      ∃ c : ℝ, 0 < c ∧
        IsEquivalent atTop (fun x : ℕ ↦ (A x : ℝ))
          (fun x : ℕ ↦ c * x / Real.sqrt (Real.log x)) := by
  sorry

end Erdos1081
