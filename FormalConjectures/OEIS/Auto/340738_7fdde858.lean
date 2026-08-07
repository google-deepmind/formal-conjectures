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

open Nat
open Filter

/--
A340738: Denominator of a sequence of fractions converging to $e$.
$a(1) = 1$
$a(2) = 2$
For $n > 2$:
If $n$ is odd: $a(n) = 2 a(n-1) + n a(n-2)$
If $n$ is even: $a(n) = \frac{n+2}{2} a(n-1) - a(n-2) - \frac{n-2}{2} a(n-3)$
-/
def A340738 : ℕ → ℕ
| 0 => 0 -- Sequence conventionally starts at index 1
| 1 => 1
| 2 => 2
| n + 3 =>
  let k := n + 3
  -- The recursive calls are safe since k ≥ 3.
  let a_prev_3 := A340738 (k - 3) -- a(k-3)
  let a_prev_2 := A340738 (k - 2) -- a(k-2)
  let a_prev_1 := A340738 (k - 1) -- a(k-1)

  -- k % 2 will be 0 for even k, and 1 for odd k.
  match k % 2 with
  | 0 => -- k is even, k ≥ 4
    -- a(k) = ((k+2)/2) * a(k-1) - a(k-2) - ((k-2)/2) * a(k-3)
    let c1 := (k + 2) / 2
    let c3 := (k - 2) / 2
    -- We rely on the property that the natural number recursion is well-defined on ℕ.
    c1 * a_prev_1 - a_prev_2 - c3 * a_prev_3
  | 1 => -- k is odd, k ≥ 3
    -- a(k) = 2 * a(k-1) + k * a(k-2)
    2 * a_prev_1 + k * a_prev_2
  | _ => 0 -- Should not happen

/--
A340737: Numerator of a sequence of fractions converging to $e$.
Uses the same recurrence as A340738 but starting with $b(1)=3, b(2)=5$.
-/
def A340737 : ℕ → ℕ
| 0 => 0
| 1 => 3
| 2 => 5
| n + 3 =>
  let k := n + 3
  let b_prev_3 := A340737 (k - 3)
  let b_prev_2 := A340737 (k - 2)
  let b_prev_1 := A340737 (k - 1)

  match k % 2 with
  | 0 => -- k is even, k ≥ 4
    let c1 := (k + 2) / 2
    let c3 := (k - 2) / 2
    c1 * b_prev_1 - b_prev_2 - c3 * b_prev_3
  | 1 => -- k is odd, k ≥ 3
    2 * b_prev_1 + k * b_prev_2
  | _ => 0

/-- The sequence of fractions $\frac{A340737(n)}{A340738(n)}$ as a sequence of real numbers.

Note: For $n \ge 1$, $A340738(n)$ is positive, so division by zero is not an issue
for the defined sequence of interest.
-/
noncomputable
def sequence_of_fractions (n : ℕ) : ℝ :=
  (A340737 n : ℝ) / (A340738 n : ℝ)

/-- oeis_340738_conjecture_0: "The convergence is conjectured."
Formally, the sequence of fractions $A340737(n) / A340738(n)$ converges to $e$.
-/
theorem oeis_340738_conjecture_0 :
  Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) :=
by sorry
