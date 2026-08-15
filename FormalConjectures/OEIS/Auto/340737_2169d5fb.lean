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

/--
A340737: Numerators of a sequence of fractions converging to $e$.
$$a(1) = 3, a(2) = 5$$
For $n > 2$:
$$a(n) = \begin{cases} \left(\frac{n+2}{2}\right) a(n-1) - a(n-2) - \left(\frac{n-2}{2}\right) a(n-3) & \text{if } n \text{ is even} \\ 2 a(n-1) + n a(n-2) & \text{if } n \text{ is odd} \end{cases}$$
-/
noncomputable def A340737 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Required for total function, O(1,1) suggests 0 is not relevant.
  | 1 => 3
  | 2 => 5
  | n' + 3 => -- n $\ge$ 3
    let n := n' + 3

    let a_nm1 := A340737 (n - 1)
    let a_nm2 := A340737 (n - 2)
    let a_nm3 := A340737 (n - 3)

    if n % 2 = 0 then
      -- n is even, n $\ge$ 4
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2

      -- $a(n) = c_1 \cdot a(n-1) - a(n-2) - c_2 \cdot a(n-3)$.
      -- We use Int.ofNat for safe subtraction, as the result is known to be positive.
      Int.toNat (Int.ofNat c1 * Int.ofNat a_nm1 - Int.ofNat a_nm2 - Int.ofNat c2 * Int.ofNat a_nm3)
    else
      -- n is odd, n $\ge$ 3
      2 * a_nm1 + n * a_nm2
termination_by n

/--
A340738: Denominators of a sequence of fractions converging to $e$.
This sequence is defined by the same recurrence relation as A340737 but with initial values $b(1)=1, b(2)=2$.
$$b(1) = 1, b(2) = 2$$
For $n > 2$:
$$b(n) = \begin{cases} \left(\frac{n+2}{2}\right) b(n-1) - b(n-2) - \left(\frac{n-2}{2}\right) b(n-3) & \text{if } n \text{ is even} \\ 2 b(n-1) + n b(n-2) & \text{if } n \text{ is odd} \end{cases}$$
-/
noncomputable def A340738 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n' + 3 => -- n $\ge$ 3
    let n := n' + 3

    let b_nm1 := A340738 (n - 1)
    let b_nm2 := A340738 (n - 2)
    let b_nm3 := A340738 (n - 3)

    if n % 2 = 0 then
      -- n is even, n $\ge$ 4
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2

      -- $b(n) = c_1 \cdot b(n-1) - b(n-2) - c_2 \cdot b(n-3)$.
      -- We use Int.ofNat for safe subtraction.
      Int.toNat (Int.ofNat c1 * Int.ofNat b_nm1 - Int.ofNat b_nm2 - Int.ofNat c2 * Int.ofNat b_nm3)
    else
      -- n is odd, n $\ge$ 3
      2 * b_nm1 + n * b_nm2
termination_by n

/--
oeis_340737_conjecture_0: The convergence is conjectured.
Formally, the sequence of fractions $\frac{\mathrm{A}340737(n)}{\mathrm{A}340738(n)}$ converges to $e$.
-/
theorem oeis_340737_conjecture_0 :
  Filter.Tendsto (fun n : ℕ => (A340737 n : ℝ) / (A340738 n : ℝ)) Filter.atTop (nhds (Real.exp 1)) :=
by sorry
