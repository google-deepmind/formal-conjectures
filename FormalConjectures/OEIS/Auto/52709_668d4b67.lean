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
A052709: Expansion of g.f. $(1-\sqrt{1-4x-4x^2})/(2(1+x))$.
The $n$-th term $a(n)$ is given by the combinatorial identity:
$$a(n) = \sum_{k=0}^{n-1} \frac{1}{k+1} \binom{2k}{k} \binom{k}{n-1-k}$$
where $\frac{1}{k+1} \binom{2k}{k}$ is the $k$-th Catalan number.
-/
def A052709 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k =>
    ((Nat.choose (2 * k) k) / (k + 1)) * (Nat.choose k (n - 1 - k))


theorem a_zero : A052709 0 = 0 := by
  sorry

theorem a_one : A052709 1 = 1 := by
  sorry

theorem a_two : A052709 2 = 1 := by
  sorry

theorem a_three : A052709 3 = 3 := by
  sorry

namespace A052709_Conjecture

open List

/-- A list of natural numbers is composed of positive integers. -/
def is_positive_list (l : List ℕ) : Prop :=
  ∀ x ∈ l, 0 < x

/-- A list covers an initial interval of positive integers if the set of
    its elements is $\{1, 2, \dots, \max(l)\}$. -/
def covers_initial_interval (l : List ℕ) : Prop :=
  is_positive_list l ∧
  let s := l.toFinset
  match s.max with
  | some max_s => ∀ m : ℕ, 0 < m → (m ∈ s ↔ m ≤ max_s)
  | none => l.isEmpty

/-- A list has a non-decreasing subsequence of length 3 (the pattern `x ≤ y ≤ z`). -/
def has_nondecreasing_pattern_3 (l : List ℕ) : Prop :=
  ∃ (i j k : Fin l.length),
    i < j ∧ j < k ∧ l.get i ≤ l.get j ∧ l.get j ≤ l.get k

/-- A list avoids the pattern `x ≤ y ≤ z` if it does not have a non-decreasing subsequence of length 3. -/
def avoids_pattern_xyz (l : List ℕ) : Prop :=
  ¬ has_nondecreasing_pattern_3 l

/-- The set of sequences of length `n-1` satisfying the conditions of the conjecture. -/
def sequences_counted_by_A052709 (n : ℕ) : Set (List ℕ) :=
  { l : List ℕ | l.length = n - 1 ∧ covers_initial_interval l ∧ avoids_pattern_xyz l }

end A052709_Conjecture

open A052709_Conjecture
open scoped Set

/--
Conjecture: For n > 0, also the number of sequences of length n - 1 covering an initial interval of
positive integers and avoiding three terms (..., x, ..., y, ..., z, ...) such that x <= y <= z.

Note: The set of such sequences is finite, as their maximum element is bounded by their length.
-/
theorem oeis_52709_conjecture_0 (n : ℕ) (h : 0 < n) [Fintype (sequences_counted_by_A052709 n)] :
    A052709 n = Fintype.card (sequences_counted_by_A052709 n) :=
  by sorry
