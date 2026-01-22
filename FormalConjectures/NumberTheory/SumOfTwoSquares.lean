/-
Copyright 2025 The Formal Conjectures Authors.

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

/-!
# Sum of Two Squares Conjecture

*Reference:* [Math StackExchange Question](https://math.stackexchange.com/questions/2376879/does-the-interval-x-x-10-x1-4-contain-a-sum-of-two-squares)
**Does the interval $[x, x + 10 x^{1/4})$ contain a sum of two squares?**

*Reference:* Bambah and Chowla, "On numbers which can be expressed as a sum of two squares",
Proc. Nat. Inst. Sci. India 13 (1947), 101–103.

This conjecture asks whether for sufficiently large $x$, the interval $[x, x + 10x^{1/4})$
always contains an integer that can be expressed as the sum of two squares.

The known result by Bambah and Chowla shows that the interval $[x, x + 2\sqrt{2}x^{1/4}]$
always contains a sum of two squares, where $2\sqrt{2} \approx 2.828 < 10$.
-/

namespace NumberTheory

open Nat Finset BigOperators

/--
A number $n$ is a sum of two squares if there exist integers $a, b$ such that $n = a^2 + b^2$.
-/
def IsSumOfTwoSquares (n : ℕ) : Prop := ∃ a b : ℤ, n = a^2 + b^2

/--
**Conjecture**: For all sufficiently large $x \in \mathbb{N}$, there exists an integer $n$
such that $x \leq n < x + 10 \cdot x^{1/4}$ and $n$ is a sum of two squares.
-/
@[category research open, AMS 11]
theorem sum_of_two_squares_conjecture :
  ∀ᶠ (x : ℕ) in Filter.atTop, ∃ n : ℕ,
    x ≤ n ∧ n < x + 10 * (x : ℝ) ^ (1/4 : ℝ) ∧ IsSumOfTwoSquares n := by
  sorry

/--
**Known Result (Bambah-Chowla)**: For all $x \in \mathbb{N}$, there exists an integer $n$
such that $x \leq n \leq x + 2\sqrt{2} \cdot x^{1/4}$ and $n$ is a sum of two squares.

This is a theorem, not a conjecture, and serves as a known bound that is
stronger than the conjecture (since $2\sqrt{2} < 10$).
-/
@[category test, AMS 11]
theorem bambam_chowla_bound :
  ∀ (x : ℕ), ∃ n : ℕ,
    x ≤ n ∧ n ≤ x + ⌈2 * Real.sqrt 2 * (x : ℝ) ^ (1/4 : ℝ)⌉ ∧ IsSumOfTwoSquares n := by
  sorry

/--
**Weaker Conjecture**: For all sufficiently large $x \in \mathbb{N}$, there exists an integer $n$
such that $x \leq n < x + C \cdot x^{1/4}$ and $n$ is a sum of two squares,
for some constant $C < 10$.

This would be an intermediate result between the known Bambah-Chowla bound
($C = 2\sqrt{2}$) and the full conjecture ($C = 10$).
-/
@[category research open, AMS 11]
theorem weaker_sum_of_two_squares_conjecture (C : ℝ) (hC : 2 * Real.sqrt 2 < C ∧ C < 10) :
  ∀ᶠ (x : ℕ) in Filter.atTop, ∃ n : ℕ,
    x ≤ n ∧ n < x + ⌈C * (x : ℝ) ^ (1/4 : ℝ)⌉ ∧ IsSumOfTwoSquares n := by
  sorry

end NumberTheory
