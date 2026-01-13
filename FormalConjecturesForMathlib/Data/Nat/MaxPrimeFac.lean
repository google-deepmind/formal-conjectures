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

import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Lattice

namespace Nat

/-- The greatest prime divisor of a natural number `n > 1`.

Takes the junk value `0` for `n = 0` and `n = 1`.

TODO Consider redefining this using the computable implementation:
`n.primeFactorsList.getLastI`. -/
noncomputable def maxPrimeFac (n : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p ∣ n}

@[simp]
lemma maxPrimeFac_zero :
    maxPrimeFac 0 = 0 := by
  simpa [maxPrimeFac] using Set.Infinite.Nat.sSup_eq_zero infinite_setOf_prime

@[simp]
lemma maxPrimeFac_one :
    maxPrimeFac 1 = 0 := by
  suffices {p : ℕ | p.Prime ∧ p = 1} = ∅ by simp [maxPrimeFac, this]
  aesop

lemma prime_maxPrimeFac_of_one_lt (n : ℕ) (h : 1 < n) :
    Prime (maxPrimeFac n) := by
  set s := {p : ℕ | p.Prime ∧ p ∣ n} with hs
  have hs₀ : s.Nonempty := by
    simp only [Set.Nonempty, Set.mem_setOf_eq, ← ne_one_iff_exists_prime_dvd, hs]
    omega
  have hs₁ : BddAbove s := by
    use n
    simp only [hs, mem_upperBounds, Set.mem_setOf_eq, and_imp]
    exact fun p _ hp ↦ Nat.le_of_dvd (zero_lt_of_lt h) hp
  exact (Nat.sSup_mem hs₀ hs₁).1

lemma maxPrimeFac_eq_of_dvd_of_le
    (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h_dvd : p ∣ n) (h_le : maxPrimeFac n ≤ p) :
    maxPrimeFac n = p := by
  refine le_antisymm h_le ?_
  replace hn : 1 < n := Nat.lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hn h_dvd)
  set s := {p : ℕ | p.Prime ∧ p ∣ n} with hs
  have hs₁ : BddAbove s := by
    use n
    simp only [hs, mem_upperBounds, Set.mem_setOf_eq, and_imp]
    exact fun p _ hp ↦ Nat.le_of_dvd (zero_lt_of_lt hn) hp
  exact ConditionallyCompleteLattice.le_csSup s p hs₁ ⟨hp, h_dvd⟩

@[simp]
lemma one_lt_maxPrimeFac_iff (n : ℕ) :
    1 < maxPrimeFac n ↔ 1 < n := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · simp only [lt_one_iff] at hn
    simp [hn]
  · simp
  · simpa [hn] using (prime_maxPrimeFac_of_one_lt n hn).one_lt

end Nat
