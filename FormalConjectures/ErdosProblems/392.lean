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
# Erdős Problem 392

*Reference:* [erdosproblems.com/392](https://www.erdosproblems.com/392)
-/
open Filter

open scoped Nat

/--
Let $A(n)$ denote the least value of $t$ such that
$$
  n! = a_1 \cdots a_t
$$
with $a_1 \leq \cdots \leq a_t\leq n^2$. Is it true that
$$
  A(n) = \frac{n}{2} - \frac{n}{2\log n} + o\left(\frac{n}{\log n}\right)?
$$
-/
@[category research open, AMS 11]
theorem erdos_392 : (∀ (A : ℕ → ℕ), (∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a t ≤ n ^ 2) }
      (A n)) →
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n))
    ↔ answer(sorry) := by
  sorry

/--
If we change the condition to $a_t \leq n$ it can be shown that
$$
  A(n) = n - \frac{n}{log n} + o\left(\frac{n}{\log n}\right)
$$
-/
@[category research solved, AMS 11]
theorem erdos_392.variants.lower (A : ℕ → ℕ)
    (hA : ∀ n > 0, IsLeast
      { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧ Monotone a ∧ a t ≤ n) }
      (A n)) :
    (fun (n : ℕ) => (A n - n + n / Real.log n : ℝ)) =o[atTop] fun n => n / Real.log n := by
  sorry
