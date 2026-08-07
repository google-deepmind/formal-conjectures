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

open BigOperators LinearRecurrence

/--
The sequence $b_n$ such that $A227582(n) = b_{n-1}$ for $n \ge 1$.
This is the 0-indexed solution to the linear recurrence in $\mathbb{Z}$.
-/
def A227582_base (n : ℕ) : ℤ :=
  let order := 7
  -- Coefficients $c_i$ for the recurrence $u_{n+7} = \sum_{i=0}^6 c_i u_{n+i}$.
  -- This corresponds to the OEIS signature $(2, -1, 0, 0, 1, -2, 1)$ which means $c_i = s_{7-i}$.
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  -- Initial values $a_0$ through $a_6$. These are {2, 7, 14, 23, 35, 50, 67}.
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

/--
A227582: Expansion of $(2+3*x+2*x^2+2*x^3+3*x^4+x^5-x^6)/(1-2x+x^2-x^5+2*x^6-x^7)$.
The sequence is 1-indexed in OEIS, so $a(n)$ is the $(n-1)$-th term of the 0-indexed solution.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : 0 < n then
    (A227582_base (n - 1)).toNat
  else
    0


theorem a_one : a 1 = 2 := by sorry
theorem a_two : a 2 = 7 := by sorry
theorem a_three : a 3 = 14 := by sorry
theorem a_four : a 4 = 23 := by sorry

/--
At A227581, it is conjectured that a(n) = floor(1/(2*H(n) - H(n^2 + n - 1) - g)),
where H denotes harmonic number and g denotes the Euler-Mascheroni constant.
-/
theorem oeis_227582_conjecture_0 (n : ℕ) (hn : 0 < n) :
    a n = (Int.floor
      (1 / (2 * (↑(harmonic n) : ℝ) -
            (↑(harmonic (n * n + n - 1)) : ℝ) -
            Real.eulerMascheroniConstant))).toNat := by
  sorry
