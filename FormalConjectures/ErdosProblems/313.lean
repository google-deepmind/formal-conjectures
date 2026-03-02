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

import FormalConjectures.Util.ProblemImports
import Mathlib.NumberTheory.LucasPrimality

/-!
# Erdős Problem 313

*References:*
- [erdosproblems.com/313](https://www.erdosproblems.com/313)
- [A54377](https://oeis.org/A54377) (Primary pseudoperfect numbers)
-/

namespace Erdos313

def erdos_313_solutions : Set (ℕ × Finset ℕ) :=
  {(m, P) | 2 ≤ m ∧ P.Nonempty ∧ (∀ p ∈ P, p.Prime) ∧ ∑ p ∈ P, (1 : ℚ) / p = 1 - 1 / m}

@[category research open, AMS 11]
theorem erdos_313_conjecture : answer(sorry) ↔ erdos_313_solutions.Infinite := by sorry

@[category test, AMS 11]
theorem erdos_313_solution_6_2_3 : (6, {2, 3}) ∈ erdos_313_solutions := by
  norm_num [erdos_313_solutions]

@[category test, AMS 11]
theorem erdos_313_solution_42_2_3_7 : (42, {2, 3, 7}) ∈ erdos_313_solutions := by
  norm_num [erdos_313_solutions]

def IsPrimaryPseudoperfect (n : ℕ) : Prop := ∃ P, (n, P) ∈ erdos_313_solutions

@[category research open, AMS 11]
theorem erdos_313.variants.primary_pseudoperfect_are_infinite :
    Set.Infinite {n | IsPrimaryPseudoperfect n} := by sorry

-- Verified fast exponentiation for Pratt certificates
@[category API]
def modPowAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, res => res
  | fuel + 1, b, e, res =>
    if e = 0 then res
    else if e % 2 = 1 then
      modPowAux m fuel ((b * b) % m) (e / 2) ((res * b) % m)
    else
      modPowAux m fuel ((b * b) % m) (e / 2) res

@[category API]
lemma modPowAux_spec (m fuel b e res : ℕ) (h_fuel : e < 2^fuel) : 
    (modPowAux m fuel b e res : ZMod m) = (res : ZMod m) * (b : ZMod m)^e := by
  induction fuel generalizing b e res with
  | zero => 
    have : e = 0 := by omega
    simp [this, modPowAux]
  | succ fuel ih =>
    rw [modPowAux]
    split_ifs with h_e h_odd
    · rw [h_e, pow_zero, mul_one]
    · have h1 : e / 2 < 2^fuel := by omega
      rw [ih _ _ _ h1]
      have he : e = 2 * (e / 2) + 1 := by omega
      rw [ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul]
      nth_rw 2 [he]
      rw [pow_add, pow_one, pow_mul]
      ring
    · have h1 : e / 2 < 2^fuel := by omega
      rw [ih _ _ _ h1]
      have he : e = 2 * (e / 2) := by omega
      rw [ZMod.natCast_mod, Nat.cast_mul]
      nth_rw 2 [he]
      rw [pow_mul]
      ring

@[category API]
def modPow (base exp m : ℕ) : ℕ :=
  if m = 1 then 0 else modPowAux m 100 (base % m) exp 1

@[category API]
lemma pow_eq_modPow (b e m : ℕ) (hm : m > 1) (he : e < 2^100) :
    (b : ZMod m)^e = (modPow b e m : ZMod m) := by
  dsimp [modPow]
  have : ¬m = 1 := by omega
  simp [this]
  rw [modPowAux_spec _ _ _ _ _ he]
  push_cast
  rw [ZMod.natCast_mod]
  ring

-- Pratt certificate for 78595501069
@[category API]
lemma factor_lemma_1 (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2^2 * (3^5 * (7 * (29 * 398323)))) : 
    q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 29 ∨ q = 398323 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_three h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hdvd

@[category API]
lemma p78 : Nat.Prime 78595501069 := by
  apply lucas_primality 78595501069 2
  · change ((2 : ℕ) : ZMod 78595501069) ^ 78595501068 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 78595501068 at hdvd
    have h_eq : 78595501068 = 2^2 * (3^5 * (7 * (29 * 398323))) := by rfl
    rw [h_eq] at hdvd
    rcases factor_lemma_1 q hq hdvd with rfl | rfl | rfl | rfl | rfl
    · change ((2 : ℕ) : ZMod 78595501069) ^ 39297750534 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 78595501069) ^ 26198500356 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 78595501069) ^ 11227928724 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 78595501069) ^ 2710189692 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((2 : ℕ) : ZMod 78595501069) ^ 197316 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

-- Pratt certificate for 1729101023519
@[category API]
lemma factor_lemma_2 (q : ℕ) (hq : q.Prime) (hdvd : q ∣ 2 * (11 * 78595501069)) : 
    q = 2 ∨ q = 11 ∨ q = 78595501069 := by
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · left; exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
  rcases hq.dvd_mul.mp hdvd with h | hdvd
  · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · right; right; exact (Nat.prime_dvd_prime_iff_eq hq p78).mp hdvd

@[category API]
lemma p8_prime : Nat.Prime 1729101023519 := by
  apply lucas_primality 1729101023519 11
  · change ((11 : ℕ) : ZMod 1729101023519) ^ 1729101023518 = 1
    rw [pow_eq_modPow]; decide; decide; decide
  · intro q hq hdvd
    change q ∣ 1729101023518 at hdvd
    have h_eq : 1729101023518 = 2 * (11 * 78595501069) := by rfl
    rw [h_eq] at hdvd
    rcases factor_lemma_2 q hq hdvd with rfl | rfl | rfl
    · change ((11 : ℕ) : ZMod 1729101023519) ^ 864550511759 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((11 : ℕ) : ZMod 1729101023519) ^ 157191002138 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide
    · change ((11 : ℕ) : ZMod 1729101023519) ^ 22 ≠ 1
      rw [pow_eq_modPow]; decide; decide; decide

@[category test, AMS 11]
theorem erdos_313_solution_2 : (2, {2}) ∈ erdos_313_solutions := by norm_num [erdos_313_solutions]

@[category test, AMS 11]
theorem erdos_313_solution_1806 : (1806, {2, 3, 7, 43}) ∈ erdos_313_solutions := by norm_num [erdos_313_solutions]

@[category test, AMS 11]
theorem erdos_313_solution_47058 : (47058, {2, 3, 11, 23, 31}) ∈ erdos_313_solutions := by norm_num [erdos_313_solutions]

@[category test, AMS 11]
theorem erdos_313_solution_2214502422 : (2214502422, {2, 3, 11, 23, 31, 47059}) ∈ erdos_313_solutions := by norm_num [erdos_313_solutions]

@[category test, AMS 11]
theorem erdos_313_solution_52495396602 : (52495396602, {2, 3, 11, 17, 101, 149, 3109}) ∈ erdos_313_solutions := by norm_num [erdos_313_solutions]

@[category test, AMS 11] 
theorem erdos_313_solution_8 : (8490421583559688410706771261086, {2, 3, 11, 23, 31, 47059, 2217342227, 1729101023519}) ∈ erdos_313_solutions := by
  dsimp [erdos_313_solutions]
  refine ⟨by decide, by decide, ?_, by norm_num⟩
  intro p hp
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact by decide
  · exact by decide
  · exact by decide
  · exact by decide
  · exact by decide
  · exact by norm_num
  · exact by norm_num
  · exact p8_prime

/--
There are at least 8 primary pseudoperfect numbers.
-/
@[category undergraduate, AMS 11]
theorem exists_at_least_eight_primary_pseudoperfect :
    8 ≤ (Set.encard {n | IsPrimaryPseudoperfect n}) := by
  let S : Finset ℕ := {2, 6, 42, 1806, 47058, 2214502422, 52495396602, 8490421583559688410706771261086}
  have hS_sub : ↑S ⊆ {n | IsPrimaryPseudoperfect n} := by
    intro n hn
    rw [Finset.mem_coe] at hn
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, erdos_313_solution_2⟩
    · exact ⟨_, erdos_313_solution_6_2_3⟩
    · exact ⟨_, erdos_313_solution_42_2_3_7⟩
    · exact ⟨_, erdos_313_solution_1806⟩
    · exact ⟨_, erdos_313_solution_47058⟩
    · exact ⟨_, erdos_313_solution_2214502422⟩
    · exact ⟨_, erdos_313_solution_52495396602⟩
    · exact ⟨_, erdos_313_solution_8⟩
  have hS_card : S.card = 8 := by decide
  have h1 : Set.encard (S : Set ℕ) = 8 := by
    rw [Set.encard_coe_eq_coe_finsetCard S]
    rw [hS_card]
    rfl
  rw [← h1]
  exact Set.encard_le_encard hS_sub

end Erdos313
