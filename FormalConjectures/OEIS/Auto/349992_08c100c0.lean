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

open Nat Finset BigOperators

/--
A349992: Number of ways to write $n$ as $x^4 + y^2 + (z^2 + 2 \cdot 4^w)/3$, where $x, y, z$ are nonnegative integers, and $w$ is 0 or 1.
The definition counts the number of quadruples $(x, y, z, w)$ in the bounded non-negative integer domain that satisfy the constraints.
-/
def A349992 (n : ℕ) : ℕ :=
  -- Using tight, but correct upper bounds for iteration variables to keep the definition computationally reasonable.
  let bound_x : ℕ := Nat.sqrt (Nat.sqrt n) + 1
  let bound_y : ℕ := Nat.sqrt n + 1
  let bound_z : ℕ := (3 * n).sqrt + 1

  (range bound_x).sum fun x =>
  (range bound_y).sum fun y =>
  (range bound_z).sum fun z =>
  (range 2).sum fun w =>
      let num_z_term : ℕ := z ^ 2 + 2 * (4 ^ w)

      -- Condition 1: The term $(z^2 + 2 \cdot 4^w)/3$ must be a natural number.
      if num_z_term % 3 = 0 then
        -- Condition 2: The sum must equal n.
        if n = x ^ 4 + y ^ 2 + num_z_term / 3 then
          1
        else
          0
      else
        0

-- Helper definition for the generalized representation.
/--
`A349992_rep (n, a, b, c, m)` is true if $n$ can be written as $a \cdot x^4 + b \cdot y^2 + (z^2 + c \cdot 4^w)/m$,
where $x, y, z$ are nonnegative integers, and $w \in \{0, 1\}$.

The equation $a x^4 + b y^2 + \frac{z^2 + c 4^w}{m} = n$ is equivalent to:
$m (a x^4 + b y^2) + (z^2 + c 4^w) = m n$, provided $m \mid (z^2 + c 4^w)$.
-/
def A349992_rep (n a b c m : ℕ) : Prop :=
  m ≠ 0 ∧
  ∃ x y z : ℕ, ∃ w : Fin 2,
  m ∣ (z ^ 2 + c * (4 ^ (w : ℕ))) ∧
  m * n = m * (a * x ^ 4 + b * y ^ 2) + (z ^ 2 + c * (4 ^ (w : ℕ)))

-- The set of tuples (a, b, c, m) specified in Conjecture 2.
def A349992_conjecture_2_tuples : Finset (ℕ × ℕ × ℕ × ℕ) :=
  List.toFinset
    [ (1, 1, 11, 12), (1, 1, 11, 60), (1, 1, 14, 15), (1, 1, 23, 24),
      (1, 1, 23, 32), (1, 1, 23, 48), (1, 2, 23, 96), (2, 1, 11, 60),
      (2, 1, 23, 24), (2, 1, 23, 48), (4, 1, 23, 48)
    ]

/--
Conjecture 2 for A349992: If $(a,b,c,m)$ is one of the ordered tuples (1,1,11,12), (1,1,11,60), (1,1,14,15), (1,1,23,24), (1,1,23,32), (1,1,23,48), (1,2,23,96), (2,1,11,60), (2,1,23,24), (2,1,23,48), (4,1,23,48), then each $n = 1, 2, 3, \dots$ can be written as $a \cdot x^4 + b \cdot y^2 + (z^2 + c \cdot 4^w)/m$, where $x, y, z$ are nonnegative integers, and $w$ is 0 or 1.
-/
theorem oeis_349992_conjecture_2 :
  ∀ (T : ℕ × ℕ × ℕ × ℕ), T ∈ A349992_conjecture_2_tuples →
  ∀ n : ℕ, n > 0 →
  match T with
  | (a, b, c, m) => A349992_rep n a b c m := by
  sorry
