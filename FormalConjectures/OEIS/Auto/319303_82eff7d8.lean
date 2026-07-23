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

/--
A319303: $a(n)$ is the value of the node of the Collatz tree encoded by the number $n$.
For any $n \ge 0$: to find the node corresponding to $n$:
- move to the root of the Collatz tree (that is, to the node with value 1),
- set $r = n$
- while $r > 0$
-       decrement $r$
-       if the current node is a branching node different from 4
-          (that is, the current node has a value $v$ such that $v > 4$ and $v+2$ is a multiple of 6)
-       then
-          if $r$ is even
-          then
-             move to the child corresponding to a halving step ($2v$)
-          else
-             move to the child corresponding to a tripling step ($(v-1)/3$)
-          end
-          divide $r$ by 2 (and round down)
-       else
-          move to the only child (this child corresponds to a halving step) ($2v$)
-       end
-   end
- the value of the ending node corresponds to $a(n)$.
-/
def a (n : ℕ) : ℕ :=
  let rec find_node (r v : ℕ) : ℕ :=
    if r = 0 then v
    else
      let r_prime := r - 1
      -- Branching node condition: v > 4 and v+2 is a multiple of 6.
      let is_branching : Prop := v > 4 ∧ (v + 2) % 6 = 0

      if is_branching then
        -- Branching node logic
        let v_next := if r_prime % 2 = 0 then 2 * v else (v - 1) / 3
        let r_next := r_prime / 2
        find_node r_next v_next
      else
        -- Non-branching node logic
        let v_next := 2 * v
        let r_next := r_prime
        find_node r_next v_next
  termination_by r
  find_node n 1

theorem a_zero : a 0 = 1 := by sorry

theorem a_one : a 1 = 2 := by sorry

theorem a_two : a 2 = 4 := by sorry

theorem a_three : a 3 = 8 := by sorry


/-- The Collatz function, $C(n) = n/2$ if $n$ is even, and $C(n) = 3n+1$ if $n$ is odd. -/
def collatz_fun (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2
  else 3 * n + 1

/--
The Collatz conjecture states that for every positive integer $n$,
repeated application of the Collatz function eventually reaches 1.
-/
def collatz_conjecture : Prop :=
  ∀ n : ℕ, n > 0 → ∃ k : ℕ, (collatz_fun^[k]) n = 1

/--
%C A319303 If the Collatz conjecture is true, then this sequence contains all positive integers.
The claim is that the set of values $\{a(n) \mid n \in \mathbb{N}\}$ equals $\mathbb{N} \setminus \{0\}$.
-/
theorem oeis_319303_conjecture_0 :
  collatz_conjecture → ∀ m : ℕ, m > 0 → ∃ n : ℕ, a n = m :=
by sorry
