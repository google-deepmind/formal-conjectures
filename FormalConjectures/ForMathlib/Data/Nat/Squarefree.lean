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

import Mathlib.Data.Nat.Squarefree
import FormalConjectures.ForMathlib.Data.Nat.Factorization.Basic

namespace Nat

/-- `n.squarefreePart` is the unique `a₀ : ℕ` such that `a₀` is squarefree and `n = a₀ * b ^ 2`,
for some `b : ℕ`. At `0` this property is not well defined because `b` must be `0` and `a₀` can be
any squarefree number; we give the junk value `1` at `n = 0` following the convention that the
squarefree part of any square is `1`. -/
def squarefreePart (n : ℕ) : ℕ := n.factorization.prod fun (p e : ℕ) ↦ p ^ (e % 2)

example : squarefreePart 2 = 2 := by
  decide +native

example : squarefreePart 5 = 5 := by
  decide +native

example : squarefreePart 4 = 1 := by
  decide +native

example : squarefreePart 8 = 2 := by
  decide +native

example : squarefreePart 16 = 1 := by
  decide +native

example : squarefreePart 24 = 6 := by
  decide +native

theorem squarefreePart_ne_zero (n : ℕ) : n.squarefreePart ≠ 0 := by
  simp [squarefreePart]

theorem squarefreePart_zero : squarefreePart 0 = 1 := by
  simp [squarefreePart]

/-- If `n` is squarefree, then its squarefree part is itself. -/
theorem squarefreePart_of_squarefree {n : ℕ} (hn : Squarefree n) :
    squarefreePart n = n := by
  nth_rw 2 [← n.factorization_prod_pow_eq_self fun _ ↦ by simp_all]
  simp only [squarefreePart, Finsupp.prod, support_factorization]
  exact Finset.prod_congr rfl fun p hp ↦ by
    rw [factorization_eq_one_of_squarefree hn (mem_primeFactors.1 hp).1 (mem_primeFactors.1 hp).2.1]

/-- The squarefree part of any square is `1`. -/
theorem squarefreePart_of_isSquare {n : ℕ} (hn : IsSquare n) :
    squarefreePart n = 1 := by
  rcases eq_or_ne n 0 with (rfl | h₀); exact squarefreePart_zero
  obtain ⟨r, rfl⟩ := hn
  rw [ne_eq, mul_eq_zero, or_self] at h₀
  rw [squarefreePart, Finsupp.prod, support_factorization,
    Finset.prod_congr rfl fun p hp ↦ by rw [r.factorization_mul h₀ h₀]]
  simp [← two_mul]

/-- If $n = \prod_p p^{e_p}$ is the prime factorization of $n$, then $\prod_p p^{e_p \pmod{2}}$
is the prime factorization of the squarefree part of $n$. -/
theorem squarefreePart_factorization (n : ℕ) {p : ℕ} (hp : p.Prime) :
    n.squarefreePart.factorization p = n.factorization p % 2 := by
  rw [squarefreePart, prod_factorization_eq_prod_primeFactors,
    n.prod_primeFactors_factorization_apply hp (f := fun p n ↦ n.factorization p % 2)
      (fun _ _ h ↦ by simp [factorization_eq_zero_of_not_dvd h]) (by simp)]

theorem Prime.squarefree {p : ℕ} (hp : p.Prime) : Squarefree p := Irreducible.squarefree hp

theorem squarefree_squarefreePart (n : ℕ) : Squarefree n.squarefreePart := by
  refine Nat.squarefree_iff_factorization_le_one n.squarefreePart_ne_zero |>.2 fun p ↦ ?_
  by_cases hp : p.Prime
  · linarith [n.squarefreePart_factorization hp, Nat.mod_lt (n.factorization p) two_pos]
  · linarith [factorization_eq_zero_of_non_prime n.squarefreePart hp]

theorem squarefreePart_dvd (n : ℕ) : squarefreePart n ∣ n := by
  rcases eq_or_ne n 0 with (rfl | h₀); simp
  exact Nat.factorization_prime_le_iff_dvd n.squarefreePart_ne_zero h₀ |>.1 fun p hp ↦
    squarefreePart_factorization _ hp ▸ Nat.mod_le _ _

/-- The square part is the value of `b ^ 2` in the squarefree decomposition of `n = a₀ * b ^ 2`.-/
def squarePart (n : ℕ) : ℕ := n / n.squarefreePart

theorem squarePart_zero : squarePart 0 = 0 := by simp [squarePart]

/-- The squarefree decomposition of a natural number. -/
theorem squarefreePart_mul_squarePart (n : ℕ) : n.squarefreePart * n.squarePart = n :=
  Nat.mul_div_eq_iff_dvd.2 n.squarefreePart_dvd

end Nat
