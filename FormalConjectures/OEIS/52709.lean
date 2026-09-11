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
# Expansion of g.f. $(1-\sqrt{1-4x-4x^2})/(2(1+x))$

The $n$-th term $a(n)$ is given by
$$a(n) = \sum_{k=0}^{n-1} \frac{1}{k+1} \binom{2k}{k} \binom{k}{n-1-k}$$

*References:*
- [A052709](https://oeis.org/A052709)-/

namespace OeisA52709

/-- $a(n) = \sum_{k=0}^{n-1} \frac{1}{k+1} \binom{2k}{k} \binom{k}{n-1-k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, ((Nat.choose (2 * k) k) / (k + 1)) * (Nat.choose k (n - 1 - k))

@[category test, AMS 5 11]
theorem a_0 : a 0 = 0 := by
  decide

@[category test, AMS 5 11]
theorem a_1 : a 1 = 1 := by
  decide

@[category test, AMS 5 11]
theorem a_2 : a 2 = 1 := by
  decide

@[category test, AMS 5 11]
theorem a_3 : a 3 = 3 := by
  decide

@[category test, AMS 5 11]
theorem a_4 : a 4 = 9 := by
  decide

@[category test, AMS 5 11]
theorem a_5 : a 5 = 31 := by
  decide

/-- A list of natural numbers is composed of positive integers. -/
def isPositiveList (l : List ℕ) : Prop :=
  ∀ x ∈ l, 0 < x

/-- A list covers an initial interval of positive integers if the set of
    its elements is $\{1, 2, \dots, \max(l)\}$. -/
def coversInitialInterval (l : List ℕ) : Prop :=
  isPositiveList l ∧
  let s := l.toFinset
  match s.max with
  | some max_s => ∀ m : ℕ, 0 < m → (m ∈ s ↔ m ≤ max_s)
  | none => l.isEmpty

/-- A list has a non-decreasing subsequence of length 3 (the pattern $x \le y \le z$). -/
def hasNondecreasingPattern3 (l : List ℕ) : Prop :=
  ∃ (i j k : Fin l.length),
    i < j ∧ j < k ∧ l.get i ≤ l.get j ∧ l.get j ≤ l.get k

/-- A list avoids the pattern $x \le y \le z$ if it does not have a non-decreasing
subsequence of length 3. -/
def avoidsPatternXYZ (l : List ℕ) : Prop :=
  ¬ hasNondecreasingPattern3 l

/-- The set of sequences of length $n-1$ satisfying the conditions of the conjecture. -/
def sequencesCountedByA052709 (n : ℕ) : Set (List ℕ) :=
  { l : List ℕ | l.length = n - 1 ∧ coversInitialInterval l ∧ avoidsPatternXYZ l }

/--
Conjecture: for $n > 0$, $a(n)$ is also the number of sequences of length $n - 1$ covering an
initial interval of positive integers and avoiding three terms
$(\dots, x, \dots, y, \dots, z, \dots)$ such that $x \le y \le z$.
- Gus Wiseman, Jun 17 2021
-/
@[category research open, AMS 5 11]
theorem conjecture (n : ℕ) (hn : 0 < n) [Fintype (sequencesCountedByA052709 n)] :
    a n = Fintype.card (sequencesCountedByA052709 n) := by
  sorry

end OeisA52709
