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

import FormalConjectures.Util.ProblemImports

/-!
# Hall's conjecture

There exists a positive number $C$ such that for any integer $x, y$ with $y^2 \ne x^3$,
$|y^2 - x^3| > C \sqrt{|x|}$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Hall%27s_conjecture)
- L. Danilov, *The Diophantine equation $x^3 - y^2 = k$ and Hall's conjecture*, Mathematical notes of the Academy of Sciences of the USSR 32 (1982): 617-618
-/

open Real

def HallIneq (C : ℝ) (e : ℝ) : Prop :=
  ∀ x y : ℤ, y ^ 2 ≠ x ^ 3 → |y ^ 2 - x ^ 3| > C * (|x| : ℝ) ^ e

def HallConjectureExp (e : ℝ) : Prop := ∃ C : ℝ, C > 0 ∧ HallIneq C e


/--
Original Hall's conjecture with exponent $1/2$.
-/
@[category research open, AMS 11]
theorem hall_conjecture : HallConjectureExp 2⁻¹ := by
  sorry

/--
Elkies' example $(x, y) = (5853886516781223, 447884928428402042307918)$ shows that such $C$ must be
less than $0.0215$. Note that simple `linarith` does not work here.
-/
@[category test, AMS 11]
theorem elkies_bound (C : ℝ) : HallIneq C 2⁻¹ → C < 0.0215 := by
  intro h
  by_cases hC : C ≤ 0
  · linarith
  · rw [HallIneq] at h
    specialize h 5853886516781223 447884928428402042307918
    simp at h
    have h1 : 76510695 < (5853886516781223 : ℝ) ^ (2 : ℝ)⁻¹ := by
      norm_num
      rw [← sqrt_eq_rpow]
      refine lt_sqrt_of_sq_lt ?_
      norm_num
    have h2 : C * 76510695 < 1641843 := by
      nlinarith
    linarith

/--
Danilov proved that one cannot replace the exponent $1/2$ with larger number.
In other words, for any $\delta > 0$, there is no positive constant $C$ such that
$|y^2 - x^3| > C |x| ^ {1/2 + \delta}$ for all integers $x, y$ with $y^2 \ne x^3$.
-/
@[category research solved, AMS 11]
theorem danilov (δ : ℝ) (h : δ > 0) : ¬ HallConjectureExp (2⁻¹ + δ) := by sorry

/--
Weak form of Hall's conjecture: relax the exponent from $1/2$ to $1/2 - \varepsilon$.
-/
@[category research open, AMS 11]
theorem weak_hall_conjecture (ε : ℝ) (hε : ε > 0) : HallConjectureExp (2⁻¹ - ε) := by
  sorry
