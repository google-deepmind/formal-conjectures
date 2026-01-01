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
# Erdős Problem 387

*References:*
 - [erdosproblems.com/387](https://www.erdosproblems.com/387)
 - [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
 - [Fa66] Faulkner, M. "On a theorem of Sylvester and Schur." Journal of the London Mathematical
    Society 1.1 (1966): 107-110.
 -
-/

open Filter

namespace Erdos387

/-- Is there an absolute constant `c > 0` such that, for all `1 ≤ k < n`, the binomial coefficient
`n.choose k` has a divisor in `(cn, n]`? -/
@[category research open, AMS 11]
theorem erdos_387 : answer(sorry) ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

@[category research solved, AMS 11]
example : ∀ i < 15, ¬ 99215 - i ∣ Nat.choose 99215 15 :=
  fun i hi => by interval_cases i <;> native_decide

/-- The following is Schinzel's conjecture, which appears in [Gu04]. -/
@[category research open, AMS 11]
theorem erdos_387.schinzel : answer(sorry) ↔
    ∀ᶠ k in atTop, ¬ IsPrimePow k → ∃ n : ℕ, ∀ i < k, ¬ n - i ∣ n.choose k := by
  sorry

/-- It is easy to see that `n.choose k` has a divisor in `[n / k, n]`.-/
@[category research solved, AMS 11]
theorem erdos_387.easy {n : ℕ+} {k : ℕ} (hk : k ≤ n) : ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.1.choose k := by
  by_cases hk0 : k = 0 <;> simp_all +decide [ Nat.factorial_ne_zero ];
  · exact PNat.one_le _;
  · refine' ⟨ Nat.gcd ( Nat.choose n k ) n, _, _ ⟩;
    · constructor;
      · rw [ div_le_iff₀ ] <;> norm_cast;
        · have h_div : (n : ℕ) ∣ Nat.choose n k * k := by
            have h_div : Nat.choose n k * k = n * Nat.choose (n - 1) (k - 1) := by
              cases n using PNat.recOn <;> cases k <;> simp_all +decide [ Nat.succ_mul_choose_eq ];
            exact ⟨ _, h_div ⟩;
          rw [ ← Nat.gcd_mul_right ];
          exact Nat.le_of_dvd ( Nat.gcd_pos_of_pos_right _ ( Nat.mul_pos n.pos ( Nat.pos_of_ne_zero hk0 ) ) ) ( Nat.dvd_gcd h_div ( dvd_mul_right _ _ ) );
        · positivity;
      · exact Nat.le_of_dvd n.pos ( Nat.gcd_dvd_right _ _ );
    · exact Nat.gcd_dvd_left _ _

/-- Is it true for any `c < 1` and all `n` sufficiently large, for all `1 ≤ k < n`, `n.choose k`
has a divisor in `(cn, n]`? This is a variant of `erdos_387` and appears in [Gu04]. -/
@[category research open, AMS 11]
theorem erdos_387.variant : answer(sorry) ↔ ∀ c : ℝ, c < 1 → ∀ᶠ n : ℕ in atTop, ∀ n k : ℕ, 1 ≤ k →
    k < n → ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

end Erdos387
