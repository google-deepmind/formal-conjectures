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

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Order.Lattice.Nat

/-!
# Least prime in an arithmetic progression

This file defines `leastPrimeInAP a d`, the smallest prime congruent to `a` modulo `d`
(returning `0` when no such prime exists), and establishes its basic membership property from
Dirichlet's theorem on primes in arithmetic progressions.
-/

@[expose] public section

/-- Minimal prime $p$ satisfying $p \equiv a \pmod d$ (evaluating to $0$ when none exists). -/
noncomputable def leastPrimeInAP (a d : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ p ≡ a [MOD d]}

/-- By Dirichlet's theorem, whenever $d \ne 0$ and $\gcd(a, d) = 1$, `leastPrimeInAP a d` is prime
and congruent to $a$ modulo $d$. -/
theorem leastPrimeInAP_prime_and_modEq {a d : ℕ} (hd : d ≠ 0) (hcop : a.Coprime d) :
    (leastPrimeInAP a d).Prime ∧ leastPrimeInAP a d ≡ a [MOD d] := by
  unfold leastPrimeInAP
  obtain ⟨p, _, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq 0 hd hcop
  exact Nat.sInf_mem (s := {p : ℕ | p.Prime ∧ p ≡ a [MOD d]}) ⟨p, hp, hmod⟩

theorem leastPrimeInAP_prime {a d : ℕ} (hd : d ≠ 0) (hcop : a.Coprime d) :
    (leastPrimeInAP a d).Prime :=
  (leastPrimeInAP_prime_and_modEq hd hcop).1

theorem leastPrimeInAP_modEq {a d : ℕ} (hd : d ≠ 0) (hcop : a.Coprime d) :
    leastPrimeInAP a d ≡ a [MOD d] :=
  (leastPrimeInAP_prime_and_modEq hd hcop).2
