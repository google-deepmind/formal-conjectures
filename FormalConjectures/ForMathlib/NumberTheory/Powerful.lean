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

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Nat.Prime.Defs

/-- Powerful number is a natural number $n$ where for every prime divisor $p$, $p^2$ divides $n$ -/
def Powerful (n : ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p ∣ n → p ^ 2 ∣ n

/-- If $n \equiv 2 \pmod{4}$, then $n$ is not powerful -/
theorem not_powerful_of_2mod4 (n : ℕ) (h : n % 4 = 2) : ¬ Powerful n := by
  rw [Powerful]
  push_neg
  use 2
  simp only [Nat.prime_two, Nat.reducePow, true_and]
  constructor
  · rw [←Nat.div_add_mod n 4, h]
    exact Nat.dvd_add (dvd_mul_of_dvd_left (by decide) (n / 4)) (dvd_refl 2)
  · intro h
    simp_all [OfNat.zero_ne_ofNat, Nat.dvd_iff_mod_eq_zero.mp h]
