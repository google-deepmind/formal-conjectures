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
# A112695

Number of steps needed to reach 4,2,1 in Collatz' 3*n+1 conjecture.

*References:*
- [A112695](https://oeis.org/A112695)
-/

namespace OeisA112695

open Function Nat

/-- The Collatz function $C(n) = 3n+1$ if $n$ is odd, $n/2$ if $n$ is even. -/
def collatz_f (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/--
The set of non-negative integers $k$ such that the $k$-th iteration of the Collatz map on $n$ is 4.
-/
def collatz_steps_to_four (n : ℕ) : Set ℕ :=
  { k : ℕ | (collatz_f^[k]) n = 4 }

/--
`a n` is the number of steps needed to reach 4,2,1 in Collatz' 3*n+1 conjecture.
$a(n)$ is the smallest $k \in \mathbb{N}$ such that $C^k(n) = 4$.
This is formally defined as the infimum of the set of such step counts.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf (collatz_steps_to_four n)

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  norm_num[a]
  delta collatz_steps_to_four
  exact (Nat.isLeast_find ⟨1,↑rfl⟩).csInf_eq

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  norm_num [a]
  delta collatz_steps_to_four
  apply Nat.isLeast_find ⟨2,by decide⟩ |>.csInf_eq

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  norm_num [a]
  use IsLeast.csInf_eq <| Nat.isLeast_find ⟨5,by tauto⟩

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  norm_num[a]
  norm_num [collatz_steps_to_four]

/--
Conjecture: a(n) = number of iterations of the Collatz 3*x+1 map applied to n until the conjectured 4,2,1 sequence is reached.
This is the statement that the value `a n` is well-defined for all positive integers $n$.
-/
@[category research open, AMS 11]
theorem conjecture : ∀ (n : ℕ), 1 ≤ n → (collatz_steps_to_four n).Nonempty := by
  sorry

end OeisA112695
