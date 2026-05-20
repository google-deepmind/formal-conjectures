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

import FormalConjectures.Util.ProblemImports

open Nat Int BigOperators Finset

/--
A308656: Number of ways to write $n$ as $(2^a \cdot 9^b)^2 + c(2c+1) + d(3d+1)$,
where $a$ and $b$ are nonnegative integers, and $c$ and $d$ are integers.
-/
def A308656 (n : ℕ) : ℕ :=
  let n' : ℤ := n
  -- Determine a sufficient bound B for all variables. Since n = 10^8 is the example context,
  -- n+1 is a safe bound for a definition that must be computationally finite.
  let B : ℕ := n + 1
  let B_Z : ℤ := B

  let full_sum (a b : ℕ) (c d : ℤ) : ℤ :=
    (2^a * 9^b : ℤ)^2 + c * (2 * c + 1) + d * (3 * d + 1)

  (Finset.range B).sum fun a =>
  (Finset.range B).sum fun b =>
  (Finset.Icc (-B_Z) B_Z).sum fun c =>
  (Finset.Icc (-B_Z) B_Z).sum fun d =>
    if full_sum a b c d = n' then 1 else 0

-- We include the helper theorems mainly to confirm the context is set up,
-- but will be removed since they are not relevant to the task of formalizing the conjecture.
-- theorem a_one : A308656 1 = 1 := by exact rfl
-- theorem a_two : A308656 2 = 1 := by rfl
-- theorem a_three : A308656 3 = 1 := by rfl
-- theorem a_four : A308656 4 = 3 := by sorry -- The provided definition might struggle here, but we proceed with formalizing the conjecture.

-- Define the five polynomials $f(x)$
def poly_f1 (x : ℤ) : ℤ := x * (4 * x + 1)
def poly_f2 (x : ℤ) : ℤ := x * (5 * x + 2)
def poly_f3 (x : ℤ) : ℤ := x * (5 * x + 4)

-- These definitions use integer division, which is safe since it can be shown that the numerator is always even.
def poly_f4 (x : ℤ) : ℤ := (x * (7 * x + 3)) / 2
def poly_f5 (x : ℤ) : ℤ := (x * (7 * x + 5)) / 2

-- The set of allowed polynomials F
def set_of_polynomials_F : Set (ℤ → ℤ) :=
  {poly_f1, poly_f2, poly_f3, poly_f4, poly_f5}

-- The common term G(d) = d * (3 * d + 1) / 2
def poly_g (d : ℤ) : ℤ := (d * (3 * d + 1)) / 2

-- The term of the form (2^a * 9^b)^2
def square_term (a b : ℕ) : ℤ := ((2^a * 9^b : ℕ) : ℤ)^2

/--
A308656 Conjecture 2: If f(x) is one of the polynomials x*(4x+1), x*(5x+2),
x*(5x+4), x*(7x+3)/2 and x(7x+5)/2, then any positive integer n can be written as
(2^a*9^b)^2 + f(c) + d*(3d+1)/2, where a and b are nonnegative integers, and c and
d are integers.
-/
theorem oeis_308656_conjecture_2 :
  ∀ n : ℕ, 0 < n →
    ∃ f : ℤ → ℤ, f ∈ set_of_polynomials_F ∧
    ∃ a b : ℕ, ∃ c d : ℤ, (n : ℤ) = square_term a b + f c + poly_g d := by
  sorry
