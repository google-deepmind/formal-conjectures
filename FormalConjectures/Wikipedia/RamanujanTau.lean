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
# Ramanujan τ-function

There are two conjectures related to the Ramanujan τ-function:

- Ramanujan-Petersson conjecture: For every prime `p`, the absolute value of the
  Ramanujan τ-function at `p` is bounded by `2 * p^(11/2)`.
- Lehmer's conjecture: The Ramanujan τ-function is never zero for any positive integer `n`.

*References:*
- [Ramanujan-Petersson conjecture](https://en.wikipedia.org/wiki/Ramanujan%E2%80%93Petersson_conjecture)
- [Lehmer's conjecture](https://en.wikipedia.org/wiki/Ramanujan_tau_function#Conjectures_on_the_tau_function)
-/

open PowerSeries PowerSeries.WithPiTopology

noncomputable def Δ : PowerSeries ℤ := X * ∏' (n : ℕ+), (1 - X ^ (n : ℕ)) ^ 24

noncomputable def τ (n : ℕ) : ℤ := PowerSeries.coeff ℤ n Δ


@[category API]
lemma multipliable : Multipliable fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ) := by
  sorry

@[category test]
lemma τ_zero : τ 0 = 0 := by simp [τ, Δ]

@[category test]
lemma τ_one : τ 1 = 1 := by
  obtain ⟨i, hi⟩ := by simpa using ((continuous_constantCoeff ℤ).tendsto _).comp multipliable.hasProd
  simp [τ, Δ, hi i]

@[category test]
lemma τ_two : τ 2 = -24 := by
  sorry


@[category research solved, AMS 11]
theorem ramanujan_petersson : ∀ p : ℕ, Prime p → abs (τ p) ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2) := by
  sorry

@[category research open, AMS 11]
theorem lehmer_ramanujan_tau : ∀ n > 0, τ n ≠ 0 := by
  sorry
