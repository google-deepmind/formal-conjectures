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
# Trajectory of $64$ under the map $n \to \text{A006368}(n)$

The map is given by
$$f(n) = \begin{cases}
3n/2 & \text{if } n \equiv 0 \pmod 2, \\
(3n+1)/4 & \text{if } n \equiv 1 \pmod 4, \\
(3n-1)/4 & \text{if } n \equiv 3 \pmod 4.
\end{cases}$$

*References:*
- [A223086](https://oeis.org/A223086)
-/

namespace OeisA223086

/-- The map $f(n) = 3n/2$ if $n$ is even, $(3n+1)/4$ if $n \equiv 1 \pmod 4$, and
$(3n-1)/4$ if $n \equiv 3 \pmod 4$. -/
def step (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else
    (3 * k - 1) / 4

/-- Trajectory of $64$ under the map `step`, indexed from $n = 1$. -/
def a (n : ℕ) : ℕ :=
  Nat.iterate step (n - 1) 64

@[category test, AMS 11]
theorem a_1 : a 1 = 64 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 96 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 144 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 216 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 324 := by rfl

@[category test, AMS 11]
theorem a_8 : a 8 = 547 := by rfl

/--
It is conjectured that this trajectory does not close on itself.
-/
@[category research open, AMS 11]
theorem conjecture (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (h : a i = a j) : i = j := by
  sorry

end OeisA223086
