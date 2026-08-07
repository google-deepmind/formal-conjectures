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

open Nat Finset

/--
A272979: Number of ways to write $n$ as $x^2 + 2y^2 + 3z^3 + 4w^4$ with $x,y,z,w$ nonnegative integers.
-/
def A272979 (n : ℕ) : ℕ :=
  -- The cardinality of the set of tuples (x, y, z, w) in ℕ^4 that satisfy the equation.
  -- We use n+1 as a loose but safe bound for all variables, as x^k <= n implies x <= n.
  -- This is guaranteed to be a finite set.
  (Finset.range (n + 1)).sum fun x =>
    (Finset.range (n + 1)).sum fun y =>
      (Finset.range (n + 1)).sum fun z =>
        (Finset.range (n + 1)).sum fun w =>
          if x^2 + 2 * y^2 + 3 * z^3 + 4 * w^4 = n then 1 else 0


theorem a_zero : A272979 0 = 1 := by
  sorry

theorem a_one : A272979 1 = 1 := by
  sorry

theorem a_two : A272979 2 = 1 := by
  sorry

theorem a_three : A272979 3 = 2 := by
  sorry


/-- The property that every natural number can be written in the form
$a x^2 + b y^2 + c z^3 + d w^4$ with $x,y,z,w$ nonnegative integers.
We require $a, b, c, d$ to be positive since they are coefficients of power terms.
-/
def full_representability (a b c d : ℕ) : Prop :=
  a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
  ∀ n : ℕ, ∃ x y z w : ℕ, a * x^2 + b * y^2 + c * z^3 + d * w^4 = n

/-- The set of 49 quadruples (a, b, c, d) conjectured by Zhi-Wei Sun to be the only ones
for which the form $a x^2 + b y^2 + c z^3 + d w^4$ is fully representable.
-/
def a272979_magic_quadruples : Set (ℕ × ℕ × ℕ × ℕ) :=
{ (1,2,1,1), (1,3,1,1), (1,6,1,1), (2,3,1,1), (2,4,1,1), (1,1,2,1), (1,4,2,1), (1,2,3,1), (1,2,4,1), (1,2,12,1),
  (1,1,1,2), (1,2,1,2), (1,3,1,2), (1,4,1,2), (1,5,1,2), (1,11,1,2), (1,12,1,2), (2,4,1,2), (3,5,1,2), (1,1,4,2),
  (1,1,1,3), (1,2,1,3), (1,3,1,3), (1,2,4,3), (1,2,1,4), (1,3,1,4), (2,3,1,4), (1,1,2,4), (1,2,2,4), (1,8,2,4),
  (1,2,3,4), (1,1,1,5), (1,2,1,5), (2,3,1,5), (2,4,1,5), (1,3,2,5), (1,1,1,6), (1,3,1,6), (1,1,2,6), (1,2,1,8),
  (1,2,4,8), (1,2,1,10), (1,1,2,10), (1,2,1,11), (2,4,1,11), (1,2,1,12), (1,1,2,13), (1,2,1,14), (1,2,1,15) }

/--
Conjecture: For positive integers a,b,c,d, any natural number can be written as
a*x^2 + b*y^2 + c*z^3 + d*w^4 with x,y,z,w nonnegative integers, if and only if (a,b,c,d)
is among the following 49 quadruples: (1,2,1,1), (1,3,1,1), (1,6,1,1), (2,3,1,1), (2,4,1,1),
(1,1,2,1), (1,4,2,1), (1,2,3,1), (1,2,4,1), (1,2,12,1), (1,1,1,2), (1,2,1,2), (1,3,1,2),
(1,4,1,2), (1,5,1,2), (1,11,1,2), (1,12,1,2), (2,4,1,2), (3,5,1,2), (1,1,4,2), (1,1,1,3),
(1,2,1,3), (1,3,1,3), (1,2,4,3), (1,2,1,4), (1,3,1,4), (2,3,1,4), (1,1,2,4), (1,2,2,4),
(1,8,2,4), (1,2,3,4), (1,1,1,5), (1,2,1,5), (2,3,1,5), (2,4,1,5), (1,3,2,5), (1,1,1,6),
(1,3,1,6), (1,1,2,6), (1,2,1,8), (1,2,4,8), (1,2,1,10), (1,1,2,10), (1,2,1,11), (2,4,1,11),
(1,2,1,12), (1,1,2,13), (1,2,1,14),(1,2,1,15).
-/
theorem oeis_a272979_conjecture_1 (a b c d : ℕ) :
  full_representability a b c d ↔ (a, b, c, d) ∈ a272979_magic_quadruples :=
by sorry
