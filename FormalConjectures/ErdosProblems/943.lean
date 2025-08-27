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
# Erdős Problem 943

*Reference:* [erdosproblems.com/943](https://www.erdosproblems.com/943)
-/

open Nat Filter

namespace Erdos943

noncomputable def a : PowerSeries ℕ := PowerSeries.mk (Set.indicator Powerful 1)

/--
Let $A$ be the set of powerful numbers. Is is true that $1_A\ast 1_A(n)=n^{o(1)}$ for every $n$?
-/
@[category research open, AMS 11]
theorem erdos_943 :
    (∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ᶠ n in atTop, (a * a).coeff ℕ  n = (n : ℝ)^(o n)) ↔
    answer(sorry) := by
  sorry

end Erdos943
