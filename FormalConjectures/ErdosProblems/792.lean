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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 792: classical bounds

*References:*
- [erdosproblems.com/792](https://www.erdosproblems.com/792)
- [Er65] Erdős, P., _Extremal problems in number theory_. Proc. Sympos. Pure Math.
  VIII (1965), 181–189, Theorem 2.
- [AlKl90] Alon, N. and Kleitman, D. J., _Sum-free subsets_. A Tribute to Paul Erdős
  (1990), 13–26, Propositions 1.1–1.2.
- [EGM14] Eberhard, S., Green, B. and Manners, F., _Sets of integers with no large
  sum-free subset_. Ann. of Math. (2) 180 (2014), 621–652.
- [Be25b] Bedert, B., _Large sum-free subsets of sets of integers via L¹-estimates
  for trigonometric series_. [arXiv:2502.08624](https://arxiv.org/abs/2502.08624).
- [Lean proof](https://github.com/AItoBit/formal-conjectures/blob/c6043b34dcb7d14de36c7e1b30f110ca67eb73b5/Main792.lean)
- [Related problem](../GreensOpenProblems/1.lean)
- [ATLAS source](https://github.com/facebookresearch/atlas-lean/blob/7f27c3ad16289716586daf311cf568bcae4160d5/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/SumFree.lean)
-/

@[expose] public section

namespace Erdos792

/-- Let $f(n)$ be maximal such that in any $A\subset \mathbb{Z}$ with $\lvert A\rvert=n$
there exists some sum-free subset $B\subseteq A$ with $\lvert B\rvert \geq f(n)$,
so that there are no solutions to $a+b=c$ with $a,b,c\in B$. Estimate $f(n)$.

This records the classical lower bound $f(n)\geq n/3$ for $n\geq2$ under the
literal integer-domain convention. The exception $n=1$ is necessary when $A=\{0\}$.
The sharp estimate beyond the known leading term remains open.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/AItoBit/formal-conjectures/blob/c6043b34dcb7d14de36c7e1b30f110ca67eb73b5/Main792.lean"]
theorem erdos_792.lower_bound (n : ℕ) (hn : 2 ≤ n) (A : Finset ℤ) (hA : A.card = n) :
    ∃ B ⊆ A, IsSumFree (B : Set ℤ) ∧ n ≤ 3 * B.card := by sorry

/-- Intervals containing zero witness the elementary upper bound $f(n)\leq n/2$.
The stronger known upper bound $f(n)\leq n/3+o(n)$, due to Eberhard, Green, and
Manners [EGM14], is not formalized here.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/AItoBit/formal-conjectures/blob/c6043b34dcb7d14de36c7e1b30f110ca67eb73b5/Main792.lean"]
theorem erdos_792.upper_bound (n : ℕ) :
    ∃ A : Finset ℤ, A.card = n ∧
      ∀ B ⊆ A, IsSumFree (B : Set ℤ) → 2 * B.card ≤ n := by sorry

/-- Alon and Kleitman [AlKl90] improved the classical lower bound to
$f(n)\geq(n+1)/3$. As in the cited literature, the ambient set excludes zero
and is nonempty. Repeated summands in the forbidden equation are allowed.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/AItoBit/formal-conjectures/blob/c6043b34dcb7d14de36c7e1b30f110ca67eb73b5/Main792.lean"]
theorem erdos_792.variants.nonzero_lower_bound (A : Finset ℤ)
    (h0 : 0 ∉ A) (hne : A.Nonempty) :
    ∃ B ⊆ A, IsSumFree (B : Set ℤ) ∧ A.card < 3 * B.card := by sorry

end Erdos792
