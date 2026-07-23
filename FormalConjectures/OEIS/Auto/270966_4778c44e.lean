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

open scoped Nat.Prime

/-- A natural number $n$ is a perfect square if its square root squared is $n$.
This is a decidable predicate since `Nat.sqrt` is computable. -/
def Nat.is_perfect_square (n : ℕ) : Prop :=
  (Nat.sqrt n) ^ 2 = n

/-- A natural number $k$ is a generalized pentagonal number if $24k+1$ is a perfect square.
This is equivalent to $k = z(3z+1)/2$ for some integer $z$. -/
def is_generalized_pentagonal (k : ℕ) : Prop :=
  (24 * k + 1).is_perfect_square

/-- Decidability instance for `is_generalized_pentagonal`. -/
instance is_generalized_pentagonal.decidable (k : ℕ) : Decidable (is_generalized_pentagonal k) :=
  by unfold is_generalized_pentagonal Nat.is_perfect_square; infer_instance

/--
A270966: Number of ways to write $n$ as $x^2 + y^2 + z(3z+1)/2$, where $x, y$ and $z$ are integers with $0 \le x \le y$ such that $x$ or $y$ has the form $p-1$ with $p$ prime.
The number of ways is the count of valid pairs $(x, y)$ because for each such pair, $k = n - x^2 - y^2$ is a generalized pentagonal number, which corresponds uniquely to an integer $z$.
-/
def A270966 (n : ℕ) : ℕ :=
  Finset.card <|
  -- We only need to iterate $x$ and $y$ up to $n$, since $x^2+y^2 \le n$.
  (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))).filter fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y

    -- 1. $x^2 + y^2 \le n$ to ensure the remainder is non-negative.
    x_sq_y_sq ≤ n ∧
    -- 2. $x \le y$.
    x ≤ y ∧
    -- 3. Primality constraint: $x$ or $y$ is $p-1$, meaning $x+1$ or $y+1$ is prime.
    (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
    -- 4. The remainder $n - (x^2 + y^2)$ must be a generalized pentagonal number.
    is_generalized_pentagonal (n - x_sq_y_sq)

-- Placeholder theorems from the prompt, kept to satisfy the instructions' context.
theorem a_one : A270966 1 = 1 := by
  sorry

theorem a_two : A270966 2 = 2 := by
  sorry

theorem a_three : A270966 3 = 2 := by
  sorry

theorem a_four : A270966 4 = 2 := by
  sorry


/--
OEIS A270966 Conjecture:
(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 49, 608.
-/
theorem oeis_270966_conjecture_i :
  (∀ n : ℕ, n > 0 → A270966 n > 0) ∧
  (∀ n : ℕ, n > 0 → (A270966 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608)) :=
by sorry
