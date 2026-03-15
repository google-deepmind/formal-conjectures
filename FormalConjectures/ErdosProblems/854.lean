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
# Erdős Problem 854

*Reference:* [erdosproblems.com/854](https://www.erdosproblems.com/854)

Let $n_k$ denote the $k$-th primorial, i.e. the product of the first $k$ primes.
If $1 = a_1 < a_2 < \cdots < a_{\varphi(n_k)} = n_k - 1$ is the sequence of integers
coprime to $n_k$, are there $\gg \max_i (a_{i+1} - a_i)$ many even integers
of the form $a_{j+1} - a_j$?

Erdős initially conjectured that all even integers up to the maximum gap appear as
consecutive differences, but computational work by Lacampagne and Selfridge for
$n_k = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13 = 30030$ produced counterexamples,
leading him to retreat to the weaker "$\gg$ many" formulation.

This was asked by Erdős in Oberwolfach (most likely in 1986) [Er85c, p.80], [Ob1].

See also OEIS sequences [A389839](https://oeis.org/A389839) and
[A048670](https://oeis.org/A048670).
-/

open Nat Finset

namespace Erdos854

/-- The $k$-th primorial: product of the first $k$ primes.
$\operatorname{primorial}(0) = 1$, $\operatorname{primorial}(1) = 2$,
$\operatorname{primorial}(2) = 6$, $\operatorname{primorial}(3) = 30$. -/
noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | k + 1 => Nat.nth Nat.Prime k * primorial k

/-- The sorted list of integers in $\{1, \ldots, n-1\}$ coprime to $n$.
We exclude 0 because the coprime sequence starts at $a_1 = 1$. -/
noncomputable def coprimeList (n : ℕ) : List ℕ :=
  ((Finset.range n).filter (fun a => 0 < a ∧ Nat.Coprime a n)).sort (· ≤ ·)

/-- Consecutive differences of a sorted list of natural numbers. -/
def consecutiveDiffs : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | a :: b :: rest => (b - a) :: consecutiveDiffs (b :: rest)

/-- The set of distinct gap values in the coprime sequence for $n$. -/
noncomputable def gapValues (n : ℕ) : Finset ℕ :=
  (consecutiveDiffs (coprimeList n)).toFinset

/-- The maximum consecutive gap in the coprime sequence for $n$.
Equivalently, one could use `List.maximum?` on the consecutive differences. -/
noncomputable def maxGap (n : ℕ) : ℕ :=
  (consecutiveDiffs (coprimeList n)).foldl max 0

/--
Erdős Problem 854 [Er85c, Ob1]:

Let $n_k$ be the $k$-th primorial. The number of distinct even integers appearing
as consecutive gaps among integers coprime to $n_k$ in $\{1, \ldots, n_k - 1\}$
is $\gg \max_i(a_{i+1} - a_i)$. That is, there exist $C > 0$ and $K_0$ such that for all
$k \geq K_0$, the number of distinct gap values is at least $C$ times the maximum gap.
-/
@[category research open, AMS 11]
theorem erdos_854 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (((gapValues (primorial k)).filter (Even ·)).card : ℝ) ≥
        C * (maxGap (primorial k) : ℝ) := by
  sorry

end Erdos854
