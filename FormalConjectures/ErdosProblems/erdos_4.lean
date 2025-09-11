/-
Copyright 2025 Google LLC

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

-- Erdos Problems URL: https://www.erdosproblems.com/4
import FormalConjectures.Util.ProblemImports

open Real

def Erdos4For (C : ℝ) : Prop :=
  {n : ℕ | Nat.nth Prime (n + 1) - Nat.nth Prime n >
    C * log (log n) * log (log (log (log n))) / (log (log (log n))) ^ 2 * log n}.Infinite

/--
Is it true that, for any $C > 0$, there infinitely many $n$ such that:
$$
  p_{n + 1} - p_n > C \frac{\log\log n\log\log\log\log n}{(\log\log\log n) ^ 2}\log n
$$

Status: Solved
-/
@[problem_status solved]
theorem erdos_4 (C : ℝ) (hC : 0 < C) :
    Erdos4For C :=
  sorry

theorem erdos_4.variants.rankin :
    ∃ C > 0, Erdos4For C :=
  sorry
