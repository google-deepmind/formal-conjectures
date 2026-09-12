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
# Erdős Problem 450

*Reference:* [erdosproblems.com/450](https://www.erdosproblems.com/450)
-/

namespace Erdos450

/-- `m` has a divisor strictly between `n` and `2n`. -/
def HasMediumDivisor (n m : ℕ) : Prop := ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ m

open scoped Classical in
/-- The number of integers strictly between `x` and `x + y` with a divisor in
`(n, 2n)`. -/
noncomputable def localCount (n x y : ℕ) : ℕ :=
  ((Finset.Ioo x (x + y)).filter (HasMediumDivisor n)).card

/-- Every window `(x, x+y)` has at most `ε y` integers with a divisor in `(n, 2n)`. -/
def UniformlySparse (ε : ℝ) (n y : ℕ) : Prop := ∀ x : ℕ, (localCount n x y : ℝ) ≤ ε * (y : ℝ)

/-- `Y ε n` is a sufficient window length: for every `ε > 0`, all large `n`, and
every `y ≥ Y ε n`, the window is `ε`-sparse. -/
def IsSufficientScale (Y : ℝ → ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ y : ℕ, Y ε n ≤ y → UniformlySparse ε n y

/-- The least window length `y₀` such that every window `(x, x+y)` with `y ≥ y₀` is
`ε`-sparse, or `⊤` if no such `y₀` exists. -/
noncomputable def windowThreshold (ε : ℝ) (n : ℕ) : ℕ∞ :=
  ⨅ y : {y : ℕ // ∀ z ≥ y, UniformlySparse ε n z}, (y.1 : ℕ∞)

/--
How large must $y=y(\epsilon,n)$ be such that the number of integers in
$(x,x+y)$ with a divisor in $(n,2n)$ is at most $\epsilon y$?

The bound is required for every $x$ and every window length at least $y$, and
$y(\epsilon,n)$ is the least such threshold (or $\infty$ if there is none).
A **linear** scale $y \le C(\epsilon) n$ is known to suffice for fixed $\epsilon$
and all large $n$ (see `erdos_450.linear_scale_suffices`).
-/
@[category research open, AMS 11]
theorem erdos_450 (ε : ℝ) (hε : 0 < ε) (n : ℕ) : windowThreshold ε n = answer(sorry) := by
  sorry

/--
A translate-uniform **linear** scale suffices: there is a sufficient window
length `Y` with `Y ε n ≤ C(ε) · n`. This is an upper bound on the optimal scale,
not the exact threshold asked for in `erdos_450`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-450/Research/TuranAnswer.lean"]
theorem erdos_450.linear_scale_suffices :
    ∃ Y : ℝ → ℕ → ℕ,
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, (Y ε n : ℝ) ≤ C * n) ∧ IsSufficientScale Y := by
  sorry

end Erdos450
