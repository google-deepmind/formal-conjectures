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

open Filter
open scoped Classical Topology

namespace Erdos450

/-- `m` has a divisor strictly between `n` and `2n`. -/
def HasMediumDivisor (n m : ℕ) : Prop := ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ m

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

/--
How large must $y=y(\epsilon,n)$ be such that the number of integers in
$(x,x+y)$ with a divisor in $(n,2n)$ is at most $\epsilon y$?

A **linear** scale is known to suffice (see `erdos_450.linear_scale_suffices`).
Whether the optimal scale is *sublinear* — a sufficient `Y` with `Y ε n = o(n)` —
is open.
-/
@[category research open, AMS 11]
theorem erdos_450 : answer(sorry) ↔
    ∃ Y : ℝ → ℕ → ℕ, IsSufficientScale Y ∧
      ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (Y ε n : ℝ) / n) atTop (𝓝 0) := by
  sorry

/--
A translate-uniform **linear** scale suffices: there is a sufficient window
length `Y` with `Y ε n ≤ C(ε) · n`. This is an upper bound on the optimal scale,
not the exact threshold asked for in `erdos_450`.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/main/starfleet/erdos-450/Research/TuranAnswer.lean"]
theorem erdos_450.linear_scale_suffices :
    ∃ Y : ℝ → ℕ → ℕ,
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, (Y ε n : ℝ) ≤ C * n) ∧ IsSufficientScale Y := by
  sorry

end Erdos450
