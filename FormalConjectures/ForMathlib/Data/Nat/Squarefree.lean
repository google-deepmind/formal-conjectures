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

namespace Nat

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

theorem squarefreePart_of_squarefree {n : ℕ} (hn : Squarefree n) :
    squarefreePart n = n := by
  by_cases h₀ : n = 0
  · simp_all only [not_squarefree_zero]
  nth_rw 2 [← n.factorization_prod_pow_eq_self h₀]
  simp only [squarefreePart, Finsupp.prod, support_factorization]
  apply Finset.prod_congr rfl fun p hp ↦ ?_
  rw [mem_primeFactors] at hp
  rw [Nat.factorization_eq_one_of_squarefree hn hp.1 hp.2.1]

theorem squarefreePart_of_isSquare {n : ℕ} (hn : IsSquare n) :
    squarefreePart n = 1 := by
  by_cases h₀ : n = 0
  · simp [h₀, squarefreePart]
  obtain ⟨r, rfl⟩ := hn
  rw [mul_eq_zero, or_self] at h₀
  rw [squarefreePart, Finsupp.prod, support_factorization,
    Finset.prod_congr rfl fun p hp ↦ by rw [r.factorization_mul h₀ h₀]]
  simp [← two_mul]
