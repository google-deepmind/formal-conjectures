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

open Nat Int

/-- The rule function for Rule 167. Inputs must be 0 or 1. -/
def ca_rule_167 (c_L c_C c_R : ℕ) : ℕ :=
  let R : ℕ := 167
  let index : ℕ := 4 * c_L + 2 * c_C + c_R
  -- Rule 167 is determined by the index-th bit of R.
  (R / (2 ^ index)) % 2

/--
The state of the Rule 167 elementary cellular automaton at time $t$ and position $x$.
The initial condition is a single ON cell at $x=0$.
$C(t, x)$ is structurally recursive on $t$.
-/
def ca_state (t : ℕ) (x : ℤ) : ℕ :=
  match t with
  | 0 => if x = 0 then 1 else 0
  | t' + 1 =>
    let C_t' (y : ℤ) := ca_state t' y
    ca_rule_167 (C_t' (x - 1)) (C_t' x) (C_t' (x + 1))

/-- The sequence of bits forming the middle column of the CA pattern, $C_{t, 0}$. -/
def middle_column_bit (t : ℕ) : ℕ := ca_state t 0

/--
A267581: Decimal representation of the middle column of the "Rule 167" elementary cellular automaton
starting with a single ON (black) cell.
The term $a(n)$ is the decimal value of the binary number $C_{0, 0} C_{1, 0} \dots C_{n, 0}$,
where $C_{i, 0}$ is the state of the center cell at time $i$.
$$a(n) = \sum_{k=0}^n C_{k, 0} \cdot 2^{n-k}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (middle_column_bit k) * (2^ (n - k))


theorem a_zero : a 0 = 1 := by sorry

theorem a_one : a 1 = 3 := by sorry

theorem a_two : a 2 = 6 := by sorry

theorem a_three : a 3 = 13 := by sorry


/-- The floor term in the conjectured recurrence relation for A267581.
This term, $\lfloor (1/2)^{(2^{n+1} \bmod n)} \rfloor$, simplifies to 1 if $(2^{n+1} \bmod n) = 0$
(i.e., $n \mid 2^{n+1}$), and 0 otherwise.
Since the recurrence is only stated for $n \ge 2$, the $n=0$ case is irrelevant to the conjecture. -/
def oeis_floor_term (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if (2 ^ (n + 1)) % n = 0 then 1 else 0

/--
A267581 conjecture on the recurrence relation.

Assuming the conjecture that the positions of the 0-bits of the middle column ("Rule 167") are given by the sequence A000051, it follows that a possible formula could be: a(n) = 2*a(n-1) + 1 - floor((1/2)^((2^(n+1)) mod n)) with a(0)=1 and a(1)=3 (Not proved, but tested up to n = 10^4). - _Andres Cicuttin_, Mar 29 2016
-/
theorem oeis_267581_conjecture_0 (n : ℕ) (hn : 2 ≤ n) :
  a n = 2 * a (n - 1) + 1 - oeis_floor_term n :=
by sorry
