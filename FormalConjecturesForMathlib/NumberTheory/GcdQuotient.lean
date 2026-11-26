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

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Gcd quotients on fixed prime supports

Definitions for the fixed-prime-support variant of Erdős problem 539.
The sharp exponent is the minimum over positive dimension splits.
-/

@[expose] public section

namespace GcdQuotient

/-- The exponent obtained by joining two positive-dimensional constructions. -/
def combineExponent (a b : ℚ) : ℚ := (a + b) / (1 + a + b)

/-- The rational exponents $u_1=1$ and
$u_d=\min_{p+s=d,\ p,s\ge1}(u_p+u_s)/(1+u_p+u_s)$ for $d\ge2$.
The unused value at zero is set to one. -/
def sharpExponent : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | n + 2 => (Finset.univ : Finset (Fin (n + 1))).inf' Finset.univ_nonempty
      (fun i ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (n + 1 - i.val)))
termination_by d => d

@[simp] theorem sharpExponent_zero : sharpExponent 0 = 1 := sharpExponent.eq_1

@[simp] theorem sharpExponent_one : sharpExponent 1 = 1 := sharpExponent.eq_2

theorem sharpExponent_rec (n : ℕ) :
    sharpExponent (n + 2) = (Finset.univ : Finset (Fin (n + 1))).inf' Finset.univ_nonempty
      (fun i ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (n + 1 - i.val))) :=
  sharpExponent.eq_3 n

/-- Exact kernel-checked value at dimension 2. -/
theorem sharpExponent_two : sharpExponent 2 = (2 / 3 : ℚ) := by
  rw [show 2 = 0 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 1 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (1 - i.val)))
      (Finset.mem_univ (⟨0, by decide⟩ : Fin 1))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i; norm_num [combineExponent, sharpExponent_one]

/-- Exact kernel-checked value at dimension 3. -/
theorem sharpExponent_three : sharpExponent 3 = (5 / 8 : ℚ) := by
  rw [show 3 = 1 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 2 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (2 - i.val)))
      (Finset.mem_univ (⟨0, by decide⟩ : Fin 2))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_two]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_two]

/-- Exact kernel-checked value at dimension 4. -/
theorem sharpExponent_four : sharpExponent 4 = (4 / 7 : ℚ) := by
  rw [show 4 = 2 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 3 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (3 - i.val)))
      (Finset.mem_univ (⟨1, by decide⟩ : Fin 3))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_two, sharpExponent_three]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_two, sharpExponent_three]

/-- A positive integer whose prime factors belong to the range of $p$.
Primality of the entries of $p$ is a separate hypothesis. -/
def SupportedOnPrimes {d : ℕ} (p : Fin d ↪ ℕ) (a : ℕ) : Prop :=
  0 < a ∧ ∀ q ∈ a.factorization.support, q ∈ Set.range p

@[simp] theorem not_supportedOnPrimes_zero {d : ℕ} (p : Fin d ↪ ℕ) :
    ¬ SupportedOnPrimes p 0 := by simp [SupportedOnPrimes]

@[simp] theorem supportedOnPrimes_one {d : ℕ} (p : Fin d ↪ ℕ) :
    SupportedOnPrimes p 1 := by simp [SupportedOnPrimes]

/-- The minimum gcd-quotient count among $n$ positive integers supported on $p$.
The natural infimum of an empty admissible class is zero. -/
noncomputable def primeSupportedMinimum {d : ℕ} (p : Fin d ↪ ℕ) (n : ℕ) : ℕ :=
  sInf {q : ℕ | ∃ A : Finset ℕ, A.card = n ∧
    (∀ a ∈ A, SupportedOnPrimes p a) ∧
      ((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b).card = q}

@[simp] theorem primeSupportedMinimum_zero {d : ℕ} (p : Fin d ↪ ℕ) :
    primeSupportedMinimum p 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le ⟨∅, by simp, by simp, by simp⟩

theorem primeSupportedMinimum_le {d n : ℕ} (p : Fin d ↪ ℕ)
    (A : Finset ℕ) (hA : A.card = n) (hS : ∀ a ∈ A, SupportedOnPrimes p a) :
    primeSupportedMinimum p n ≤ ((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b).card :=
  Nat.sInf_le ⟨A, hA, hS, rfl⟩

end GcdQuotient
