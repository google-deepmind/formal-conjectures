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
module

public import FormalConjecturesUtil

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

@[expose] public section

namespace RamanujanTau

open PowerSeries PowerSeries.WithPiTopology

noncomputable def Δ : PowerSeries ℤ := X * ∏' (n : ℕ+), (1 - X ^ (n : ℕ)) ^ 24

noncomputable def τ (n : ℕ) : ℤ := PowerSeries.coeff n Δ


@[category API, AMS 11]
lemma multipliable : Multipliable fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ) :=
  multipliable_pnat_iff_multipliable_succ (f := fun n : ℕ ↦ ((1 - X ^ n) ^ 24 : PowerSeries ℤ))
    |>.mpr ((multipliable_one_sub_X_pow ℤ).pow 24)

@[category test, AMS 11]
lemma τ_zero : τ 0 = 0 := by simp [τ, Δ]

@[category test, AMS 11]
lemma τ_one : τ 1 = 1 := by
  obtain ⟨i, hi⟩ := by simpa using ((continuous_constantCoeff ℤ).tendsto _).comp multipliable.hasProd
  simp [τ, Δ, hi i]

@[category test, AMS 11]
lemma τ_two : τ 2 = -24 := by
  -- Only the `n = 1` factor contributes to the `X`-coefficient of the product; eventual
  -- constancy of the convergent product transfers this to `Δ`.
  have key : ∀ s : Finset ℕ+,
      coeff 1 (∏ n ∈ s, ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ)) =
        if 1 ∈ s then -24 else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, coeff_one_mul, ih, coeff_one_pow]
      rcases eq_or_ne a 1 with rfl | h
      · simp [ha, coeff_one]
      · have h' : (a : ℕ) ≠ 1 := by simpa using h
        simp [coeff_one, coeff_X_pow, h.symm, h'.symm]
  obtain ⟨i, hi⟩ := by
    simpa using ((continuous_coeff ℤ 1).tendsto _).comp multipliable.hasProd
  have h2 := hi (insert 1 i) (Finset.subset_insert _ _)
  rw [key] at h2
  simp only [Finset.mem_insert_self, if_pos] at h2
  simp [τ, Δ, show (2 : ℕ) = 1 + 1 from rfl, coeff_succ_X_mul, ← h2]


/-- The Ramanujan-Petersson conjecture: $|\tau(p)| \le 2 p^{11/2}$ for primes $p$. -/
@[category research solved, AMS 11]
theorem ramanujan_petersson : ∀ p : ℕ, Prime p → abs (τ p) ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2) := by
  sorry

/-- Lehmer's conjecture: $\tau(n) \ne 0$ for all $n > 0$. -/
@[category research open, AMS 11]
theorem lehmer_ramanujan_tau : ∀ n > 0, τ n ≠ 0 := by
  sorry

end RamanujanTau
