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
# Erdős Problem 4

*Reference:* [erdosproblems.com/4](https://www.erdosproblems.com/4)
-/

open Real

def Erdos4For (C : ℝ) : Prop :=
  {n : ℕ | (n + 1).nth Nat.Prime  - n.nth Nat.Prime >
    C * log (log n) * log (log (log (log n))) / (log (log (log n))) ^ 2 * log n}.Infinite

/--
Is it true that, for any $C > 0$, there infinitely many $n$ such that:
$$
  p_{n + 1} - p_n > C \frac{\log\log n\log\log\log\log n}{(\log\log\log n) ^ 2}\log n
$$
-/
@[category research solved, AMS 11]
theorem erdos_4 : (∀ C > 0, Erdos4For C) ↔ answer(True) := by
  sorry

@[category research solved, AMS 11]
theorem erdos_4.variants.rankin :
    ∃ C > 0, Erdos4For C := by
  sorry
