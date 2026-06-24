/-
Copyright 2026 Google LLC

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

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

def B_seq (d : ℕ) : ℕ → ℕ
| 0 => 16 % d
| n + 1 => ((B_seq d n) ^ 1024) % d

def B_orbit (d : ℕ) : List ℕ :=
  (List.range 20).map (B_seq d)

lemma B_seq_in_orbit (d : ℕ)
  (h_step : ∀ x ∈ B_orbit d, (x ^ 1024) % d ∈ B_orbit d) (n : ℕ) :
  B_seq d n ∈ B_orbit d := by
  induction' n with n ih
  · have h0 : 0 ∈ List.range 20 := by decide
    exact List.mem_map.mpr ⟨0, h0, rfl⟩
  · exact h_step _ ih

lemma B_seq_eq_pow (d : ℕ) (n : ℕ) : (B_seq d n : ZMod d) = (16 : ZMod d) ^ (1024 ^ n) := by
  induction' n with n ih
  · rw [B_seq, pow_zero, pow_one]
    exact ZMod.natCast_mod 16 d
  · rw [B_seq]
    have h1 : (((B_seq d n) ^ 1024) % d : ZMod d) = ((B_seq d n) ^ 1024 : ℕ) := ZMod.natCast_mod _ d
    rw [h1]
    push_cast
    rw [ih]
    have h2 : 1024 ^ (n + 1) = 1024 ^ n * 1024 := rfl
    rw [h2, ←pow_mul]

lemma zmod_eq_zero_iff_dvd (n m : ℕ) [CharP (ZMod m) m] : (n : ZMod m) = 0 ↔ m ∣ n := by
  exact CharP.cast_eq_zero_iff (ZMod m) m n

lemma X_not_div (d : ℕ) [NeZero d]
  (h_step : ∀ x ∈ B_orbit d, (x ^ 1024) % d ∈ B_orbit d)
  (h_safe : ∀ x ∈ B_orbit d, (4 * x + 3) % d ≠ 0) (n : ℕ) :
  (2 : ZMod d) ^ (2 ^ (10 * n + 2) + 2) + 3 ≠ 0 := by
  have h_in := B_seq_in_orbit d h_step n
  have h_safe_n := h_safe _ h_in
  intro H
  have H2 : (4 * (B_seq d n : ZMod d) + 3) = 0 := by
    have h_pow := B_seq_eq_pow d n
    rw [h_pow]
    have h1 : (16 : ZMod d) = (2 : ZMod d) ^ 4 := by norm_num
    have h2 : (4 : ZMod d) = (2 : ZMod d) ^ 2 := by norm_num
    rw [h1, ←pow_mul, h2, ←pow_add]
    have h3 : 2 + 4 * 1024 ^ n = 2 ^ (10 * n + 2) + 2 := by
      have hx : 2 ^ (10 * n + 2) = 2 ^ (10 * n) * 2 ^ 2 := by rw [pow_add]
      have hy : 2 ^ (10 * n) = (2 ^ 10) ^ n := by rw [pow_mul]
      have hz : 2 ^ 10 = 1024 := by norm_num
      have hw : 2 ^ 2 = 4 := by norm_num
      rw [hx, hy, hz, hw]
      ring
    rw [h3]
    exact H
  have H3 : ((4 * B_seq d n + 3 : ℕ) : ZMod d) = 0 := by
    push_cast
    exact H2
  have _ : CharP (ZMod d) d := ZMod.charP d
  have H4 : d ∣ 4 * B_seq d n + 3 := (zmod_eq_zero_iff_dvd _ d).mp H3
  have H5 : (4 * B_seq d n + 3) % d = 0 := Nat.mod_eq_zero_of_dvd H4
  exact h_safe_n H5

def orbit_step_ok (d : ℕ) : Bool :=
  let orbit := B_orbit d
  orbit.all fun x => decide ((x ^ 1024) % d ∈ orbit)

def orbit_safe_ok (d : ℕ) : Bool :=
  let orbit := B_orbit d
  orbit.all fun x => decide ((4 * x + 3) % d ≠ 0)

lemma extract_props (d : ℕ) (hd1 : 2 ≤ d) (hd2 : d ≤ 66) :
  orbit_step_ok d = true ∧ orbit_safe_ok d = true := by
  interval_cases d <;> decide

lemma step_of_ok (d : ℕ) (h : orbit_step_ok d = true) :
  ∀ x ∈ B_orbit d, (x ^ 1024) % d ∈ B_orbit d := by
  intro x hx
  have h1 := List.all_eq_true.mp h x hx
  exact of_decide_eq_true h1

lemma safe_of_ok (d : ℕ) (h : orbit_safe_ok d = true) :
  ∀ x ∈ B_orbit d, (4 * x + 3) % d ≠ 0 := by
  intro x hx
  have h1 := List.all_eq_true.mp h x hx
  exact of_decide_eq_true h1

lemma not_dvd_of_le_66 (n : ℕ) (d : ℕ) (hd1 : 2 ≤ d) (hd2 : d ≤ 66) :
  ¬ d ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  have ⟨h1, h2⟩ := extract_props d hd1 hd2
  have h_step := step_of_ok d h1
  have h_safe := safe_of_ok d h2
  have _ : NeZero d := ⟨by omega⟩
  have h_not_zero := X_not_div d h_step h_safe n
  intro h_dvd
  have _ : CharP (ZMod d) d := ZMod.charP d
  have h_eq_zero : ( (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ℕ) : ZMod d ) = 0 := by
    exact (zmod_eq_zero_iff_dvd _ d).mpr h_dvd
  have h_cast : ( (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ℕ) : ZMod d ) =
    (2 : ZMod d) ^ (2 ^ (10 * n + 2) + 2) + 3 := by
    push_cast
    rfl
  rw [h_cast] at h_eq_zero
  exact h_not_zero h_eq_zero

lemma B_seq_67_eq_16 (n : ℕ) : B_seq 67 n = 16 := by
  induction' n with n ih
  · rfl
  · rw [B_seq, ih]
    rfl

lemma dvd_67 (n : ℕ) : 67 ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) := by
  have H : (4 * B_seq 67 n + 3) % 67 = 0 := by
    rw [B_seq_67_eq_16]
  have _ : CharP (ZMod 67) 67 := ZMod.charP 67
  have H2 : ((4 * B_seq 67 n + 3 : ℕ) : ZMod 67) = 0 := by
    exact (zmod_eq_zero_iff_dvd _ 67).mpr (Nat.dvd_of_mod_eq_zero H)
  have H3 : 4 * (B_seq 67 n : ZMod 67) + 3 = 0 := by
    push_cast at H2
    exact H2
  rw [B_seq_eq_pow] at H3
  have h1 : (16 : ZMod 67) = (2 : ZMod 67) ^ 4 := by norm_num
  rw [h1, ←pow_mul] at H3
  have h2 : (4 : ZMod 67) = (2 : ZMod 67) ^ 2 := by norm_num
  rw [h2, ←pow_add] at H3
  have h3 : 2 + 4 * 1024 ^ n = 2 ^ (10 * n + 2) + 2 := by
    have hx : 2 ^ (10 * n + 2) = 2 ^ (10 * n) * 2 ^ 2 := by rw [pow_add]
    have hy : 2 ^ (10 * n) = (2 ^ 10) ^ n := by rw [pow_mul]
    have hz : 2 ^ 10 = 1024 := by norm_num
    have hw : 2 ^ 2 = 4 := by norm_num
    rw [hx, hy, hz, hw]
    ring
  rw [h3] at H3
  have h_cast : ( (2 ^ (2 ^ (10 * n + 2) + 2) + 3 : ℕ) : ZMod 67 ) =
    (2 : ZMod 67) ^ (2 ^ (10 * n + 2) + 2) + 3 := by
    push_cast
    rfl
  rw [←h_cast] at H3
  exact (zmod_eq_zero_iff_dvd _ 67).mp H3
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) : a (10 * n + 2) = 67 := by
  -- EVOLVE-BLOCK-START
  have h_dvd := dvd_67 n
  have h_not_dvd := not_dvd_of_le_66 n
  have h_prime : Nat.Prime 67 := by decide
  have hX_ne_one : 2 ^ (2 ^ (10 * n + 2) + 2) + 3 ≠ 1 := by
    intro h
    have h2 : 2 ^ (2 ^ (10 * n + 2) + 2) + 3 ≥ 3 := by exact Nat.le_add_left 3 _
    rw [h] at h2
    revert h2
    decide
  have h_prime_mf := Nat.minFac_prime hX_ne_one
  have hX_minFac_le : (2 ^ (2 ^ (10 * n + 2) + 2) + 3).minFac ≤ 67 :=
    Nat.minFac_le_of_dvd h_prime.two_le h_dvd
  have hX_minFac_ge : 67 ≤ (2 ^ (2 ^ (10 * n + 2) + 2) + 3).minFac := by
    clear h_dvd
    by_contra! h_lt
    have h_div : (2 ^ (2 ^ (10 * n + 2) + 2) + 3).minFac ∣ (2 ^ (2 ^ (10 * n + 2) + 2) + 3) :=
      Nat.minFac_dvd _
    have h2 : 2 ≤ (2 ^ (2 ^ (10 * n + 2) + 2) + 3).minFac := h_prime_mf.two_le
    have h_le_66 : (2 ^ (2 ^ (10 * n + 2) + 2) + 3).minFac ≤ 66 := by omega
    have h_not := h_not_dvd ((2 ^ (2 ^ (10 * n + 2) + 2) + 3).minFac) h2 h_le_66
    exact h_not h_div
  exact le_antisymm hX_minFac_le hX_minFac_ge
  -- EVOLVE-BLOCK-END
