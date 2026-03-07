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
# Erdős Problem 390

*References:*
 - [erdosproblems.com/390](https://www.erdosproblems.com/390)
 - [EGS82] Erdős, P., R. K. Guy, and J. L. Selfridge. "Another Property of 239 and some related
    questions." Congr. Numer. 34 (1982): 243-257.
 -
-/

open scoped Nat
open Filter Asymptotics Real

namespace Erdos390

/-- Let `f n` be the smallest integer for which `n!` can be represented as the product of distinct
integers greater than n, the largest of which is `f n`. -/
noncomputable def f (n : ℕ) : ℕ := sInf {m : ℕ | ∃ k, ∃ f : ℕ → ℕ, StrictMono f ∧
  n < f 0 ∧ f (k - 1) = m ∧ ∏ i < k, f i = n !}

/-- `f n - 2 * n = θ (n / log n)`. This is proved in [EGS82]. -/
@[category research solved, AMS 11]
theorem erdos_390.variants.theta :
    (fun n => f n - 2 * n : ℕ → ℝ) =Θ[atTop] (fun n => n / log (n : ℝ)) := by
  sorry

/-- Does there exists a constant `c` such that `f n - 2 * n ~ c * (n / log n)`? -/
@[category research open, AMS 11]
theorem erdos_390 :
    answer(sorry) ↔ ∃ c,
      (fun n => f n - 2 * n : ℕ → ℝ) ~[atTop] (fun n => c * n / log (n : ℝ)) := by
  sorry

end Erdos390
