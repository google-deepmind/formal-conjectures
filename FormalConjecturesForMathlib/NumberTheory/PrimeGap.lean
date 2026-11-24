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


public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

/--
The prime gap: the difference between the $n+1$-th and $n$-th prime.
-/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

@[simp]
theorem primeGap_zero : primeGap 0 = 1 := by
  rw [primeGap, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

@[simp]
theorem primeGap_one : primeGap 1 = 2 := by
  rw [primeGap, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

/--
The maximal prime gap starting strictly below $x$, i.e.,
$\max_{p_n < x} (p_{n+1} - p_n)$ ($0$ when $x \le 2$).
-/
noncomputable def sup_primeGap (x : ℝ) : ℕ :=
  (Finset.range (Nat.primeCounting' ⌈x⌉₊)).sup primeGap

theorem sup_primeGap_mono : Monotone sup_primeGap := by
  intro x y hxy
  exact Finset.sup_mono (Finset.range_mono (Nat.monotone_primeCounting' (Nat.ceil_mono hxy)))

theorem sup_primeGap_eq_zero_of_le_two {x : ℝ} (hx : x ≤ 2) : sup_primeGap x = 0 := by
  unfold sup_primeGap
  have hceil : ⌈x⌉₊ ≤ 2 := Nat.ceil_le.mpr (by exact_mod_cast hx)
  have hpc : Nat.primeCounting' ⌈x⌉₊ = 0 := by
    have hle : Nat.primeCounting' ⌈x⌉₊ ≤ Nat.primeCounting' 2 :=
      Nat.monotone_primeCounting' hceil
    have h2 : Nat.primeCounting' 2 = 0 := by decide
    omega
  simp [hpc]
