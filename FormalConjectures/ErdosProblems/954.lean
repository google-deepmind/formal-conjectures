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

/-!
# Erdős Problem 954

*Reference:* [erdosproblems.com/954](https://www.erdosproblems.com/954)

Let $0 = a_0 < a_1 < a_2 < \cdots$ be the Rosen sequence, where each $a_{k+1}$ is the
smallest integer $n$ such that the number of pairs $(i,j)$ with $0 \le i \le j \le k$,
$j \ge 1$, and $a_i + a_j \le n$ is strictly less than $n$. Is the total pair count
$R(x) = \#\{(i,j) : i \le j,\, j \ge 1,\, a_i + a_j \le x\}$ equal to
$x + O(x^{1/4 + o(1)})$?

[Er77c] Erdős, P., *Problems and results in combinatorial number theory*, p.71.
-/

open Finset BigOperators Filter

namespace Erdos954

/--
Count of pairs $(i,j)$ with $1 \le j \le k$, $0 \le i \le j$, and $a(i) + a(j) \le n$.
Used in the recursive definition of the Rosen sequence.
-/
def rosenPairCount (a : ℕ → ℕ) (k n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1),
    if j = 0 then 0
    else ((Finset.range (j + 1)).filter fun i => a i + a j ≤ n).card

/--
Total count of pairs $(i,j)$ with $i \le j$, $j \ge 1$, from the full infinite
sequence, such that $a(i) + a(j) \le x$. For a strictly increasing sequence
on $\mathbb{N}$, $a(j) \ge j$, so restricting $j \le x$ suffices.
-/
def rosenPairCountTotal (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (x + 1),
    if j = 0 then 0
    else ((Finset.range (j + 1)).filter fun i => a i + a j ≤ x).card

/--
The Rosen sequence property: $a(0) = 0$, the sequence is strictly increasing,
and each $a(k+1)$ is the smallest integer $n$ such that the pair count with
respect to the first $k+1$ terms is strictly less than $n$.
-/
def IsRosenSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ StrictMono a ∧
  ∀ k, (∀ m, m < a (k + 1) → m ≤ rosenPairCount a k m) ∧
       rosenPairCount a k (a (k + 1)) < a (k + 1)

/--
Erdős Problem 954 [Er77c, p.71]:

Let $0 = a_0 < a_1 < a_2 < \cdots$ be the sequence defined by $a_0 = 0$ and $a_{k+1}$ is
the smallest integer $n$ for which the number of pairs $(i,j)$ with
$0 \le i \le j \le k$, $j \ge 1$, and $a_i + a_j \le n$ is strictly less than $n$.

The sequence begins $0, 1, 3, 5, 9, 13, 17, 24, 31, 38, 45, \ldots$ (OEIS A390642).

Is the total pair count $R(x) = \#\{(i,j) : i \le j,\, j \ge 1,\, a_i + a_j \le x\}$
equal to $x + O(x^{1/4 + o(1)})$?

By construction $R(x) \ge x$ always. Erdős and Rosen could not even prove
whether $R(x) \le (1 + o(1))x$.
-/
@[category research open, AMS 5 11]
theorem erdos_954 :
    answer(sorry) ↔
      ∀ a : ℕ → ℕ, IsRosenSequence a →
        ∀ ε : ℝ, 0 < ε →
          ∃ C : ℝ, 0 < C ∧ ∀ᶠ (x : ℕ) in atTop,
            abs ((rosenPairCountTotal a x : ℝ) - (x : ℝ)) ≤
              C * (x : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  sorry

end Erdos954
