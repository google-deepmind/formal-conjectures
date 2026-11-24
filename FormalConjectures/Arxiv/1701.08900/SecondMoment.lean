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
module

public import FormalConjecturesUtil

/-!
# Pittel's second-moment conjecture for nearly balanced markets

*Reference:* B. Pittel, [On Likely Solutions of the Stable Matching Problem with Unequal Numbers
of Men and Women](https://arxiv.org/abs/1701.08900) (2017), unnumbered conjecture on
[page 7](https://arxiv.org/pdf/1701.08900#page=7), following Theorem 1.3.

There are $n$ firms and $n+d_n$ workers with complete independent uniform strict preferences.
Every partner is preferable to being unmatched.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Arxiv.«1701.08900»

open StableMarriage.Unbalanced

/--
Pittel conjectures that if $d_n \ge 1$ and $d_n/n \to 0$, then the second moment of the number
$S_n$ of stable matchings is $O((\mathbb{E}[S_n])^2)$. The bound may depend on the sequence $d_n$.
-/
@[category research open, AMS 5 60 91]
theorem second_moment (d : ℕ → ℕ) (hd : ∀ n, 1 ≤ d n)
    (hd_limit : Tendsto (fun n ↦ (d n : ℝ) / n) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      secondMomentNumStableMatchings n (n + d n) ≤
        C * (expectedNumStableMatchings n (n + d n)) ^ 2 := by
  sorry

/-- Pittel's second-moment conjecture for a market with exactly one more worker than firm. -/
@[category research open, AMS 5 60 91]
theorem second_moment_one_extra_worker :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      secondMomentNumStableMatchings n (n + 1) ≤
        C * (expectedNumStableMatchings n (n + 1)) ^ 2 := by
  sorry

end Arxiv.«1701.08900»
