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
# Erdős Problem 1099

*Reference:* [erdosproblems.com/1099](https://www.erdosproblems.com/1099)
-/

open Filter Finset Real
open scoped Topology

namespace Erdos1099

/-- The ordered list of positive divisors of `n`. -/
def orderedDivisors (n : ℕ) : List ℕ :=
  n.divisors.sort (· ≤ ·)

/-- Consecutive ratios of a strictly increasing list of positive integers. -/
noncomputable def consecutiveRatioGaps : List ℕ → List ℝ
  | a :: b :: rest => ((b : ℝ) / a - 1) :: consecutiveRatioGaps (b :: rest)
  | _ => []

/-- $h_\alpha(n)=\sum_i (d_{i+1}/d_i-1)^\alpha$ over consecutive divisors of $n$. -/
noncomputable def h (α : ℝ) (n : ℕ) : ℝ :=
  (consecutiveRatioGaps (orderedDivisors n)).map (fun t ↦ t ^ α) |>.sum

/--
Let $1=d_1<\cdots<d_{\tau(n)}=n$ be the divisors of $n$, and for $\alpha>1$ let
$$
h_\alpha(n) = \sum_i \left( \frac{d_{i+1}}{d_i}-1\right)^\alpha.
$$
Is it true that
$$
\liminf_{n\to \infty}h_\alpha(n) \ll_\alpha 1?
$$
-/
@[category research open, AMS 11]
theorem erdos_1099 :
    answer(sorry) ↔
      ∀ α > (1 : ℝ), ∃ C : ℝ, 0 < C ∧ liminf (fun n : ℕ ↦ h α n) atTop ≤ C := by
  sorry

end Erdos1099
