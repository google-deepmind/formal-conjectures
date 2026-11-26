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

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Counting Primes in Arithmetic Progressions

This file defines `Nat.primeCountingMod`, counting primes $p \le x$ in a residue class modulo $q$.
-/

@[expose] public section

namespace Nat

/-- $\pi(x; q, a)$: the number of primes $p \le x$ satisfying $p \equiv a \pmod q$. -/
def primeCountingMod (x q : ℕ) (a : ZMod q) : ℕ :=
  ((Finset.range (x + 1)).filter fun p : ℕ => p.Prime ∧ (p : ZMod q) = a).card

@[simp]
theorem primeCountingMod_zero (q : ℕ) (a : ZMod q) : primeCountingMod 0 q a = 0 := by
  simp [primeCountingMod, Nat.not_prime_zero]

@[simp]
theorem primeCountingMod_one (q : ℕ) (a : ZMod q) : primeCountingMod 1 q a = 0 := by
  simp [primeCountingMod, Finset.range_add_one, Nat.not_prime_zero, Nat.not_prime_one]

theorem primeCountingMod_mono (q : ℕ) (a : ZMod q) : Monotone (primeCountingMod · q a) := by
  intro m n hmn
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.range_mono (Nat.add_le_add_right hmn 1)))

theorem primeCountingMod_le_primeCounting (x q : ℕ) (a : ZMod q) :
    primeCountingMod x q a ≤ x.primeCounting := by
  rw [← primesLE_card_eq_primeCounting, primeCountingMod]
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  exact mem_primesLE.mpr ⟨Nat.lt_succ_iff.mp hp.1, hp.2.1⟩

theorem primeCountingMod_natCast_eq_card_filter_mod (x q r : ℕ) :
    primeCountingMod x q r =
      ((Finset.Icc 1 x).filter fun p : ℕ => p.Prime ∧ p % q = r % q).card := by
  unfold primeCountingMod
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hp_lt, hp_prime, hp_mod⟩
    refine ⟨⟨hp_prime.pos, Nat.lt_succ_iff.mp hp_lt⟩, hp_prime, ?_⟩
    rcases eq_or_ne q 0 with rfl | hq
    · simp only [Nat.mod_zero]
      exact Int.ofNat.inj hp_mod
    · exact (ZMod.natCast_eq_natCast_iff p r q).mp hp_mod
  · rintro ⟨⟨_, hp_le⟩, hp_prime, hp_mod⟩
    refine ⟨Nat.lt_succ_of_le hp_le, hp_prime, ?_⟩
    rcases eq_or_ne q 0 with rfl | hq
    · simp only [Nat.mod_zero] at hp_mod
      simp [hp_mod]
    · exact (ZMod.natCast_eq_natCast_iff p r q).mpr hp_mod

end Nat
