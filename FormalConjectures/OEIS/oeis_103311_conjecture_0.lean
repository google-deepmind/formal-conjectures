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
A103311: A transform of the Fibonacci numbers.
The sequence $a(n)$ satisfies the linear recurrence relation:
$$a(n) = 3a(n-1) - 4a(n-2) + 2a(n-3) - a(n-4)$$
with initial terms $a(0)=0, a(1)=1, a(2)=1, a(3)=0$.
The sequence takes values in $\mathbb{Z}$.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| 2 => 1
| 3 => 0
| n + 4 => 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n

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
def f (n : ℕ) : ℤ := Nat.fib n

lemma f_0 : f 0 = 0 := rfl
lemma f_1 : f 1 = 1 := rfl
lemma f_add_two (n : ℕ) : f (n + 2) = f (n + 1) + f n := by
  have h : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have h2 : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by omega
  exact congrArg Int.ofNat h2

lemma f_id1 (m : ℕ) : f (m + 5) = 3 * f (m + 3) - f (m + 1) := by
  have h1 : f (m + 5) = f (m + 4) + f (m + 3) := f_add_two (m + 3)
  have h2 : f (m + 4) = f (m + 3) + f (m + 2) := f_add_two (m + 2)
  have h3 : f (m + 3) = f (m + 2) + f (m + 1) := f_add_two (m + 1)
  omega

lemma f_id2 (m : ℕ) : f (m + 6) = 3 * f (m + 5) - 4 * f (m + 3) + f (m + 1) := by
  have h1 : f (m + 6) = f (m + 5) + f (m + 4) := f_add_two (m + 4)
  have h2 : f (m + 5) = f (m + 4) + f (m + 3) := f_add_two (m + 3)
  have h3 : f (m + 4) = f (m + 3) + f (m + 2) := f_add_two (m + 2)
  have h4 : f (m + 3) = f (m + 2) + f (m + 1) := f_add_two (m + 1)
  omega

lemma f_id4 (m : ℕ) : f (m + 6) = 2 * f (m + 5) - f (m + 3) := by
  have h1 : f (m + 6) = f (m + 5) + f (m + 4) := f_add_two (m + 4)
  have h2 : f (m + 5) = f (m + 4) + f (m + 3) := f_add_two (m + 3)
  omega

lemma f_id5 (m : ℕ) : f (m + 3) = 2 * f (m + 1) + f m := by
  have h1 : f (m + 3) = f (m + 2) + f (m + 1) := f_add_two (m + 1)
  have h2 : f (m + 2) = f (m + 1) + f m := f_add_two m
  omega

def P (k : ℕ) : Prop :=
  a (5 * k) = (-1 : ℤ)^k * f (5 * k) ∧
  a (5 * k + 1) = (-1 : ℤ)^k * f (5 * k + 1) ∧
  a (5 * k + 2) = (-1 : ℤ)^k * f (5 * k + 1) ∧
  a (5 * k + 3) = 0 ∧
  a (5 * k + 4) = (-1 : ℤ)^(k + 1) * f (5 * k + 3)

lemma a_5k_5 (k : ℕ) : a (5 * k + 5) = 3 * a (5 * k + 4) - 4 * a (5 * k + 3) + 2 * a (5 * k + 2) - a (5 * k + 1) := by
  have : 5 * k + 5 = (5 * k + 1) + 4 := by omega
  rw [this, a]

lemma a_5k_6 (k : ℕ) : a (5 * k + 6) = 3 * a (5 * k + 5) - 4 * a (5 * k + 4) + 2 * a (5 * k + 3) - a (5 * k + 2) := by
  have : 5 * k + 6 = (5 * k + 2) + 4 := by omega
  rw [this, a]

lemma a_5k_7 (k : ℕ) : a (5 * k + 7) = 3 * a (5 * k + 6) - 4 * a (5 * k + 5) + 2 * a (5 * k + 4) - a (5 * k + 3) := by
  have : 5 * k + 7 = (5 * k + 3) + 4 := by omega
  rw [this, a]

lemma a_5k_8 (k : ℕ) : a (5 * k + 8) = 3 * a (5 * k + 7) - 4 * a (5 * k + 6) + 2 * a (5 * k + 5) - a (5 * k + 4) := by
  have : 5 * k + 8 = (5 * k + 4) + 4 := by omega
  rw [this, a]

lemma a_5k_9 (k : ℕ) : a (5 * k + 9) = 3 * a (5 * k + 8) - 4 * a (5 * k + 7) + 2 * a (5 * k + 6) - a (5 * k + 5) := by
  have : 5 * k + 9 = (5 * k + 5) + 4 := by omega
  rw [this, a]

lemma pow_succ_m1 (k : ℕ) : (-1 : ℤ)^(k + 1) = (-1 : ℤ)^k * -1 := by ring
lemma pow_succ_succ_m1 (k : ℕ) : (-1 : ℤ)^(k + 2) = (-1 : ℤ)^k := by
  calc (-1 : ℤ)^(k + 2) = (-1 : ℤ)^k * (-1)^2 := by ring
  _ = (-1 : ℤ)^k * 1 := by norm_num
  _ = (-1 : ℤ)^k := by ring

lemma P_holds (k : ℕ) : P k := by
  induction k with
  | zero =>
    have a0 : a 0 = (-1 : ℤ)^0 * f 0 := by rfl
    have a1 : a 1 = (-1 : ℤ)^0 * f 1 := by rfl
    have a2 : a 2 = (-1 : ℤ)^0 * f 1 := by rfl
    have a3 : a 3 = 0 := by rfl
    have a4 : a 4 = (-1 : ℤ)^1 * f 3 := by rfl
    exact ⟨a0, a1, a2, a3, a4⟩
  | succ k ih =>
    rcases ih with ⟨h0, h1, h2, h3, h4⟩
    have a5 : a (5 * k + 5) = (-1 : ℤ)^(k + 1) * f (5 * k + 5) := by
      rw [a_5k_5 k, h4, h3, h2, h1]
      have id1 := f_id1 (5 * k)
      have eq : 3 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 3)) - 4 * 0 + 2 * ((-1 : ℤ) ^ k * f (5 * k + 1)) - (-1 : ℤ) ^ k * f (5 * k + 1) = (-1 : ℤ) ^ (k + 1) * (3 * f (5 * k + 3) - f (5 * k + 1)) := by
        rw [pow_succ_m1 k]
        ring
      rw [eq, ← id1]
    have a6 : a (5 * k + 6) = (-1 : ℤ)^(k + 1) * f (5 * k + 6) := by
      rw [a_5k_6 k, a5, h4, h3, h2]
      have id2 := f_id2 (5 * k)
      have eq : 3 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 5)) - 4 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 3)) + 2 * 0 - (-1 : ℤ) ^ k * f (5 * k + 1) = (-1 : ℤ) ^ (k + 1) * (3 * f (5 * k + 5) - 4 * f (5 * k + 3) + f (5 * k + 1)) := by
        rw [pow_succ_m1 k]
        ring
      rw [eq, ← id2]
    have a7 : a (5 * k + 7) = (-1 : ℤ)^(k + 1) * f (5 * k + 6) := by
      rw [a_5k_7 k, a6, a5, h4, h3]
      have id4 := f_id4 (5 * k)
      have eq : 3 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 6)) - 4 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 5)) + 2 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 3)) - 0 = (-1 : ℤ) ^ (k + 1) * f (5 * k + 6) + (-1 : ℤ) ^ (k + 1) * 2 * (f (5 * k + 6) - (2 * f (5 * k + 5) - f (5 * k + 3))) := by
        ring
      rw [eq, id4]
      ring
    have a8 : a (5 * k + 8) = 0 := by
      rw [a_5k_8 k, a7, a6, a5, h4]
      have id4 := f_id4 (5 * k)
      have eq : 3 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 6)) - 4 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 6)) + 2 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 5)) - (-1 : ℤ) ^ (k + 1) * f (5 * k + 3) = (-1 : ℤ) ^ (k + 1) * (- f (5 * k + 6) + (2 * f (5 * k + 5) - f (5 * k + 3))) := by
        ring
      rw [eq, ← id4]
      ring
    have a9 : a (5 * k + 9) = (-1 : ℤ) ^ (k + 2) * f (5 * k + 8) := by
      rw [a_5k_9 k, a8, a7, a6, a5]
      have id5 := f_id5 (5 * k + 5)
      have eq : 3 * 0 - 4 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 6)) + 2 * ((-1 : ℤ) ^ (k + 1) * f (5 * k + 6)) - (-1 : ℤ) ^ (k + 1) * f (5 * k + 5) = (-1 : ℤ) ^ (k + 2) * (2 * f (5 * k + 6) + f (5 * k + 5)) := by
        rw [pow_succ_succ_m1 k, pow_succ_m1 k]
        ring
      rw [eq, ← id5]
    have p0 : a (5 * (k + 1)) = (-1 : ℤ) ^ (k + 1) * f (5 * (k + 1)) := by
      have e : 5 * (k + 1) = 5 * k + 5 := by omega
      rw [e]
      exact a5
    have p1 : a (5 * (k + 1) + 1) = (-1 : ℤ) ^ (k + 1) * f (5 * (k + 1) + 1) := by
      have e : 5 * (k + 1) + 1 = 5 * k + 6 := by omega
      rw [e]
      exact a6
    have p2 : a (5 * (k + 1) + 2) = (-1 : ℤ) ^ (k + 1) * f (5 * (k + 1) + 1) := by
      have e1 : 5 * (k + 1) + 2 = 5 * k + 7 := by omega
      have e2 : 5 * (k + 1) + 1 = 5 * k + 6 := by omega
      rw [e1, e2]
      exact a7
    have p3 : a (5 * (k + 1) + 3) = 0 := by
      have e : 5 * (k + 1) + 3 = 5 * k + 8 := by omega
      rw [e]
      exact a8
    have p4 : a (5 * (k + 1) + 4) = (-1 : ℤ) ^ (k + 1 + 1) * f (5 * (k + 1) + 3) := by
      have e1 : 5 * (k + 1) + 4 = 5 * k + 9 := by omega
      have e2 : k + 1 + 1 = k + 2 := by omega
      have e3 : 5 * (k + 1) + 3 = 5 * k + 8 := by omega
      rw [e1, e2, e3]
      exact a9
    exact ⟨p0, p1, p2, p3, p4⟩

lemma natAbs_m1_pow (k : ℕ) : Int.natAbs ((-1 : ℤ)^k) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Int.natAbs_mul, ih]
    rfl

lemma natAbs_mul_m1_pow (k m : ℕ) : Int.natAbs ((-1 : ℤ)^k * f m) = Nat.fib m := by
  rw [Int.natAbs_mul, natAbs_m1_pow k]
  have h : Int.natAbs (f m) = Nat.fib m := rfl
  rw [h]
  omega
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) : ∃ m : ℕ, Int.natAbs (a n) = Nat.fib m := by
  -- EVOLVE-BLOCK-START
  have hP := P_holds (n / 5)
  have r_cases : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hP with ⟨h0, h1, h2, h3, h4⟩
  rcases r_cases with r0 | r1 | r2 | r3 | r4
  · have hn' : n = 5 * (n / 5) := by omega
    rw [hn']
    use 5 * (n / 5)
    rw [h0, natAbs_mul_m1_pow]
  · have hn' : n = 5 * (n / 5) + 1 := by omega
    rw [hn']
    use 5 * (n / 5) + 1
    rw [h1, natAbs_mul_m1_pow]
  · have hn' : n = 5 * (n / 5) + 2 := by omega
    rw [hn']
    use 5 * (n / 5) + 1
    rw [h2, natAbs_mul_m1_pow]
  · have hn' : n = 5 * (n / 5) + 3 := by omega
    rw [hn']
    use 0
    rw [h3]
    rfl
  · have hn' : n = 5 * (n / 5) + 4 := by omega
    rw [hn']
    use 5 * (n / 5) + 3
    rw [h4, natAbs_mul_m1_pow]
  -- EVOLVE-BLOCK-END
