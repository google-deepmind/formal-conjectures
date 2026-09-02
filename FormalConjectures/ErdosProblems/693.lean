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
# Erdős Problem 693

*References:*
- [erdosproblems.com/693](https://www.erdosproblems.com/693)
- [Er79e] Erdős, Paul, *Some unconventional problems in number theory*.
  Astérisque (1979), 73–82.

See also [Erdős problem 446](https://www.erdosproblems.com/446).
-/

namespace Erdos693

open Filter

/-- The finite set $A \subseteq [n,n^k]$ from Erdős problem 693. -/
def divisorWindowSet (k n : ℕ) : Finset ℕ :=
  (Finset.Icc n (n ^ k)).filter fun x ↦
    ((Finset.Ioo n (2 * n)).filter fun d ↦ d ∣ x).Nonempty

/-- $x$ and $y$ are consecutive elements of a finite set of natural numbers. -/
def ConsecutiveIn (A : Finset ℕ) (x y : ℕ) : Prop :=
  x ∈ A ∧ y ∈ A ∧ x < y ∧
    ∀ z, z ∈ A → x < z → z < y → False

/-- The maximum gap in the finite set $A$ is at most $B$. -/
def MaxGapAtMost (A : Finset ℕ) (B : ℝ) : Prop :=
  ∀ x y, ConsecutiveIn A x y → (y - x : ℝ) ≤ B

/-- For $k=n=2$, the divisor-window set is exactly $\{3\}$. -/
@[category test, AMS 11]
theorem divisorWindowSet_two_two : divisorWindowSet 2 2 = {3} := by
  rfl

/-- Let $k \geq 2$ and let $n$ be sufficiently large depending on $k$. Let
$A = \{a_1 < a_2 < \cdots\}$ be the set of integers in $[n,n^k]$ which have a divisor in
$(n,2n)$. Is $\max_i (a_{i+1} - a_i) \leq (\log n)^{O(1)}$? -/
@[category research open, AMS 11]
theorem erdos_693 : answer(sorry) ↔ ∀ k ≥ 2, ∃ C : ℕ, ∀ᶠ n in atTop,
    MaxGapAtMost (divisorWindowSet k n) ((Real.log (n : ℝ)) ^ C) := by
  sorry

end Erdos693
