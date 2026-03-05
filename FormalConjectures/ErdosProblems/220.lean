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
# Erdős Problem 220

Is it true that the sum of squared gaps between consecutive totatives of $n$ is
$O(n^2 / \varphi(n))$?

*Reference:* [erdosproblems.com/220](https://www.erdosproblems.com/220)

[MoVa86] Montgomery, H.L. and Vaughan, R.C., _On the distribution of reduced residues_, 1986.
-/

open Finset

namespace Erdos220

/-- The sum of squared consecutive gaps in a sorted list of natural numbers. -/
def sumSquaredGaps : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)

/-- The totatives of $n$ listed in increasing order: all $m$ with $1 \le m < n$
and $\gcd(m, n) = 1$. -/
def sortedTotatives (n : ℕ) : List ℕ :=
  ((Finset.range n).filter (fun m => 0 < m ∧ Nat.Coprime m n)).sort (· ≤ ·)

/--
Erdős Problem 220 [Er40, Er55c, Er57, Er61, Er65b, Er73, Er79, ErGr80, Er81k, Er85c]:

Let $n \ge 1$ and $A = \{a_1 < \cdots < a_{\varphi(n)}\} = \{1 \le m < n : \gcd(m,n) = 1\}$ be the
totatives of $n$ listed in increasing order. Is it true that
$$\sum_{1 \le k < \varphi(n)} (a_{k+1} - a_k)^2 \ll n^2 / \varphi(n)?$$

The answer is yes, as proved by Montgomery and Vaughan [MoVa86], who showed
the more general result that for any $\gamma \ge 1$,
$$\sum_{1 \le k < \varphi(n)} (a_{k+1} - a_k)^\gamma \ll n^\gamma / \varphi(n)^{\gamma-1}.$$
-/
@[category research solved, AMS 11]
theorem erdos_220 :
    answer(True) ↔
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (sumSquaredGaps (sortedTotatives n) : ℝ) ≤ C * (n : ℝ) ^ 2 / (Nat.totient n : ℝ) := by
  sorry

end Erdos220
