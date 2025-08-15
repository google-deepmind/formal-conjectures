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

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.PrimeFin

namespace Nat

/--
A natural number $n$ is said to be $k$-full if for every prime factor $p$ of $n$, the $k$-th power
$p^k$ also divides $n$.
-/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

instance Nat.Full.decide : ∀ k n, Decidable (Full k n) := by
  intro k n
  dsimp [Full]
  infer_instance

/--
A [Powerful number](https://en.wikipedia.org/wiki/Powerful_number) is a natural number $n$ where
for every prime divisor $p$, $p^2$ divides $n$.
Powerful numbers are also known as "squareful", "square-full", or "$2$-full".
-/
abbrev Powerful : ℕ → Prop := (2).Full

instance Nat.Powerful.decide : ∀ n, Decidable (Powerful n) := by
  intro n
  dsimp [Powerful, Full]
  apply Finset.decidableDforallFinset

theorem full_of_le_full (k : ℕ) (n : ℕ) {m : ℕ} (hk : k ≤ m) (h : m.Full n) : k.Full n :=
  fun p a ↦ pow_dvd_of_le_of_pow_dvd hk (h p a)

/-- If $n \equiv p \pmod{p ^ (k + 1)}$, for a prime $p$ then $n$ is not $(k + 1)$-full.-/
theorem not_full_of_prime_mod_prime_sq (n : ℕ) (k : ℕ) {p : ℕ} (hp : p.Prime)
    (h : n % p ^ (k + 1) = p) : ¬ (k + 1).Full n := by
  rw [Full]
  push_neg
  use p
  simp  [mem_primeFactors, hp, ne_eq, true_and, reducePow]
  constructor
  · rw [←Nat.div_add_mod n (p ^ (k + 1)), h]
    have : p ∣ p ^ (k + 1) := by exact Dvd.intro_left (p.pow k) rfl
    simp [Nat.dvd_add (dvd_mul_of_dvd_left this (n / (p ^ 2))) (dvd_refl p)]
    exact ⟨Dvd.dvd.mul_right this (n / p ^ (k + 1)), fun a ↦ Prime.ne_zero hp⟩
  · intro h
    simp_all [OfNat.zero_ne_ofNat, Nat.dvd_iff_mod_eq_zero.mp h]
    aesop
