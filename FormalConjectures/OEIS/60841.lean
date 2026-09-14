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
# Numerator of $1/\det(M)$ for $M[i,j] = 1/\operatorname{lcm}(i,j)$

Numerator of $1/\det(M)$ where $M$ is the $n \times n$ matrix with
$M[i,j] = 1/\operatorname{lcm}(i,j)$.

*References:*
- [A060841](https://oeis.org/A060841)-/

namespace OeisA60841

/-- The $n \times n$ matrix with entry $(i,j)$ equal to
$1/\operatorname{lcm}(i+1, j+1)$ over $\mathbb{Q}$. -/
def lcmMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j : Fin n ↦ 1 / ((Nat.lcm (i.val + 1) (j.val + 1) : ℚ))

/-- Numerator of $1/\det(M)$ where $M$ is the $n \times n$ matrix with
$M[i,j] = 1/\operatorname{lcm}(i+1,j+1)$. -/
def a (n : ℕ) : ℤ :=
  ((lcmMatrix n).det)⁻¹.num

@[category test, AMS 11 15]
theorem a_1 : a 1 = 1 := by
  decide +native

@[category test, AMS 11 15]
theorem a_2 : a 2 = 4 := by
  decide +native

@[category test, AMS 11 15]
theorem a_3 : a 3 = 18 := by
  decide +native

@[category test, AMS 11 15]
theorem a_4 : a 4 = 144 := by
  decide +native

@[category test, AMS 11 15]
theorem a_5 : a 5 = 900 := by
  decide +native

/-- The exceptional values of $n$ where $1/\det(M)$ is conjectured to be an integer. -/
def integerDetN : Set ℕ :=
  Set.Icc 1 34 ∪ {36, 38}

/--
"Conjecture: $1/\det(M)$ is an integer only for n: 1 to 34, 36 and 38.
All denominators are powers of two (A000079). - _Robert G. Wilson v_, Aug 02 2015"-/
@[category research open, AMS 11 15]
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → (((lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ integerDetN)) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, ((lcmMatrix n).det)⁻¹.den = 2 ^ k) := by
  sorry

end OeisA60841
