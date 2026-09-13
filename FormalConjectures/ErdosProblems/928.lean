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
# Erdős Problem 928

*Reference:* [erdosproblems.com/928](https://www.erdosproblems.com/928)
-/

open Set

namespace Erdos928

/-- Integers `n` whose largest prime factor is `< n^α` and that of `n+1` is `< (n+1)^β`. -/
def SmoothPair (α β : ℝ) : Set ℕ :=
  { n : ℕ | 1 < n ∧
      ((n.maxPrimeFac : ℝ) < (n : ℝ) ^ α) ∧
      (((n + 1).maxPrimeFac : ℝ) < ((n + 1 : ℕ) : ℝ) ^ β) }

/--
Let $\alpha,\beta\in (0,1)$ and let $P(n)$ denote the largest prime divisor of $n$. Does the
density of integers $n$ such that $P(n)<n^{\alpha}$ and $P(n+1)<(n+1)^\beta$ exist?
-/
@[category research open, AMS 11]
theorem erdos_928 :
    answer(sorry) ↔
      ∀ α ∈ Ioo (0 : ℝ) 1, ∀ β ∈ Ioo (0 : ℝ) 1,
        ∃ d : ℝ, (SmoothPair α β).HasDensity d := by
  sorry

end Erdos928
