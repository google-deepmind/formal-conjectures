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
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The map is $f(n)$:
$$f(n) = \begin{cases} 3n/2 & \text{if } n \equiv 0 \pmod 2 \\ (3n+1)/4 & \text{if } n \equiv 1 \pmod 4 \\ (3n-1)/4 & \text{if } n \equiv 3 \pmod 4 \end{cases}$$
-/
def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

/--
A223086: Trajectory of 64 under the map $n \to A006368(n)$.
The sequence $a(n)$ is 1-indexed by $a(1)=64$ and recurrence $a(n+1) = f(a(n))$.
The $n$-th term is $f^{n-1}(64)$.
-/
def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64


theorem a_one : a 1 = 64 := by
  constructor

theorem a_two : a 2 = 96 := by
  constructor

theorem a_three : a 3 = 144 := by
  constructor

theorem a_four : a 4 = 216 := by
  constructor

/--
It is conjectured that this trajectory does not close on itself.
This is equivalent to stating that the sequence is injective on positive indices.
-/
theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  sorry
