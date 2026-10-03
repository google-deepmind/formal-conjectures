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

import FormalConjecturesUtil

/-!
# Determinant of prime sum indicator matrix

Determinant of the $n \times n$ matrix with $(i,j)$-entry ($1 \le i, j \le n$) equal to $1$
if $i + j$ is prime, and $0$ otherwise.

*References:*
- [A069191](https://oeis.org/A069191)
-/

namespace OeisA69191

open Matrix

/-- The $n \times n$ matrix $M(n)$ with $(i,j)$-entry ($1 \le i, j \le n$) equal to $1$
if $i + j$ is prime, and $0$ otherwise. -/
def primeMatrix (R : Type*) [Zero R] [One R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if Nat.Prime (i.val + j.val + 2) then 1 else 0

/-- Determinant of the $n \times n$ matrix with $(i,j)$-entry ($1 \le i, j \le n$) equal to $1$
if $i + j$ is prime, and $0$ otherwise. -/
def a (n : ℕ) : ℤ :=
  (primeMatrix ℤ n).det

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = -1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by native_decide

@[category test, AMS 11]
theorem a_6 : a 6 = -1 := by native_decide

@[category test, AMS 11]
theorem a_7 : a 7 = -4 := by native_decide

/--
Conjecture: Let $M(n)$ be the $n \times n$ matrix with $(i,j)$-entry equal to $1$ or $0$ according as
$i + j$ is prime or not. For each $n = 24, 25, \dots$, the characteristic polynomial of $M(n)$ is
irreducible over the field of rational numbers, and the $n$ eigenvalues can be listed as
$\lambda(1), \dots, \lambda(n)$ such that
$\lambda(1) > -\lambda(2) > \lambda(3) > -\lambda(4) > \dots > (-1)^{n-1} \lambda(n) > 0$.
- _Zhi-Wei Sun_, Aug 25 2013
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 24 ≤ n) :
    Irreducible (primeMatrix ℚ n).charpoly ∧
    ∃ ev : Fin n → ℝ,
      (primeMatrix ℝ n).charpoly = ∏ i : Fin n, (Polynomial.X - Polynomial.C (ev i)) ∧
      StrictAnti (fun i : Fin n => (-1 : ℝ) ^ (i : ℕ) * ev i) ∧
      ∀ i : Fin n, 0 < (-1 : ℝ) ^ (i : ℕ) * ev i := by
  sorry

end OeisA69191
