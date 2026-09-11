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
open scoped Topology

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

/--
How large must $y=y(\epsilon,n)$ be such that the number of integers in
$(x,x+y)$ with a divisor in $(n,2n)$ is at most $\epsilon y$?

A **linear** scale is known to suffice (see `erdos_450.linear_scale_suffices`).

With `UniformlySparse` quantifying over *every* window start `x`, a **sublinear** scale
cannot suffice, for a trivial reason: the window `(n, n + y)` with `y ≤ n` is full, since each of
its integers lies in `(n, 2n)` and divides itself. So `Y ε n = o(n)` fails already at `ε = 1/2`,
and this statement holds with `answer(False)`. This settles the formal statement only; the
question Erdős asked is unaffected (erdosproblems.com notes the intended quantifier on `x` is
unclear). See `erdos_450.variants.far_windows` for the version with windows beyond `2n`.
-/
@[category research solved, AMS 11]
theorem erdos_450 : answer(False) ↔
    ∃ Y : ℝ → ℕ → ℕ, IsSufficientScale Y ∧
      ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (Y ε n : ℝ) / n) atTop (𝓝 0) := by
  refine iff_of_false not_false ?_
  rintro ⟨Y, hY, hlim⟩
  obtain ⟨N, hN⟩ := hY (1 / 2) (by norm_num)
  obtain ⟨M, hM⟩ := eventually_atTop.1
    ((tendsto_order.1 (hlim (1 / 2) (by norm_num))).2 (1 / 2) (by norm_num))
  set n := max (max N M) 3 with hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
  have hnM : M ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn3 : 3 ≤ n := le_max_right _ _
  have hYn : Y (1 / 2) n ≤ n := by
    have h := hM n hnM
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [div_lt_iff₀ hnpos] at h
    exact_mod_cast (show (Y (1 / 2) n : ℝ) < n by linarith).le
  set y := max (Y (1 / 2) n) 3 with hy
  have hy3 : 3 ≤ y := le_max_right _ _
  have hyn : y ≤ n := max_le hYn hn3
  -- The window `(n, n + y)` is full: every element is its own divisor in `(n, 2n)`.
  have hfull : localCount n n y = y - 1 := by
    classical
    unfold localCount
    rw [Finset.filter_true_of_mem, Nat.card_Ioo]
    · omega
    · intro m hm
      rw [Finset.mem_Ioo] at hm
      exact ⟨m, hm.1, by omega, dvd_rfl⟩
  have hsp := hN n hnN y (le_max_left _ _) n
  rw [hfull, Nat.cast_sub (by omega), Nat.cast_one] at hsp
  have : (3 : ℝ) ≤ y := by exact_mod_cast hy3
  linarith

/-- Every window `(x, x+y)` starting at or beyond `2n` has at most `ε y` integers with a
divisor in `(n, 2n)`. Such windows contain no element of `(n, 2n)` itself, which removes the
trivial obstruction to `erdos_450`. -/
def UniformlySparseFar (ε : ℝ) (n y : ℕ) : Prop :=
  ∀ x : ℕ, 2 * n ≤ x → (localCount n x y : ℝ) ≤ ε * (y : ℝ)

/-- `Y ε n` is a sufficient window length for windows beyond `2n`. -/
def IsSufficientFarScale (Y : ℝ → ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ y : ℕ, Y ε n ≤ y → UniformlySparseFar ε n y

/--
The sublinear-scale question for windows that lie beyond `(n, 2n)`: is there a sufficient
`Y` with `Y ε n = o(n)` once windows starting inside `(n, 2n)` are excluded? This is the
reading of `erdos_450` that is not settled by the trivial full window.
-/
@[category research open, AMS 11]
theorem erdos_450.variants.far_windows : answer(sorry) ↔
    ∃ Y : ℝ → ℕ → ℕ, IsSufficientFarScale Y ∧
      ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (Y ε n : ℝ) / n) atTop (𝓝 0) := by
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
