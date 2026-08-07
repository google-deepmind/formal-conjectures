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

open BigOperators Finset Nat

/--
A352286: Number of ways to write $n$ as $w + x^2 + 2y^2 + 3z^2 + x \cdot y \cdot z$, where $w$ is $0$ or $1$, and $x,y,z$ are nonnegative integers.
$$a(n) = \left| \left\{ (w, x, y, z) \in \{0, 1\} \times \mathbb{N}^3 \mid n = w + x^2 + 2y^2 + 3z^2 + xyz \right\} \right|$$
-/
def A352286 (n : ℕ) : ℕ :=
  let B : Finset ℕ := range (n + 1)
  (range 2).sum (fun w =>
    B.sum (fun x =>
      B.sum (fun y =>
        B.sum (fun z =>
          if n = w + x^2 + 2 * y^2 + 3 * z^2 + x * y * z then 1 else 0))))

def A352286_exceptions : Set ℕ := {106, 744, 5469, 331269}

/--
Conjecture 1: a(n) = 0 if and only if $n \in \{106, 744, 5469, 331269\}$.
-/
theorem oeis_352286_conjecture_1 :
  ∀ n : ℕ, (A352286 n = 0 ↔ n ∈ A352286_exceptions) := by
  sorry
