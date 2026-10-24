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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 880

*References:*
- [erdosproblems.com/880](https://www.erdosproblems.com/880)
- [Er98] Erdős, Paul, *Some of my new and almost new problems and results in combinatorial number
  theory*. Number theory (Eger, 1996) (1998), 169-180.
- [HHP07] Hegyvári, Norbert and Hennecart, François and Plagne, Alain, *Answer to a question by
  Burr and Erdős on restricted addition, and related results*. Combin. Probab. Comput. (2007),
  747-756.
-/

@[expose] public section

open Filter Set

namespace Erdos880

/-- The set of integers which are the sum of `k` or fewer distinct elements of `A`. -/
def restrictedSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, (s : Set ℕ) ⊆ A ∧ s.card ≤ k ∧ ∑ a ∈ s, a = n}

/--
`B = {b₁ < b₂ < ⋯}` has bounded gaps: `b_{n+1} - b_n = O(1)`, where `b_n` is the `n`-th
element of `B` (as `Nat.nth`).
-/
def HasBoundedGaps (B : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ n, Nat.nth (· ∈ B) (n + 1) - Nat.nth (· ∈ B) n ≤ C

/--
Let $A\subset\mathbb{N}$ be an additive basis of order $k$. Let $B=\{b_1<b_2<\cdots\}$ be the set
of integers which are the sum of $k$ or fewer distinct $a\in A$. Is it true that
$b_{n+1}-b_n=O(1)$? (Where the implied constant may depend on both $A$ and $k$.)

A problem of Burr and Erdős.

Hegyvári, Hennecart, and Plagne [HHP07] showed the answer is yes for $k=2$ (in fact with
$b_{n+1}-b_n\leq 2$ for large $n$) but no for $k\geq 3$.

The proof that $b_{n+1}-b_n\leq 2$ for $k=2$ is trivial, since clearly all odd numbers in $A+A$
must be the sum of two distinct elements from $A$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos880.lean#L777"]
theorem erdos_880 : answer(False) ↔
    ∀ (k : ℕ) (A : Set ℕ), A.IsAsymptoticAddBasisOfOrder k →
      HasBoundedGaps (restrictedSums A k) := by
  sorry

/--
Hegyvári, Hennecart, and Plagne [HHP07] showed that for $k\geq 3$ there is an additive basis $A$
of order $k$ for which the sums of at most $k$ distinct elements do not have bounded gaps.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos880.lean#L777"]
theorem erdos_880.variants.three_or_more : ∀ k : ℕ, 3 ≤ k → ∃ A : Set ℕ,
    A.IsAsymptoticAddBasisOfOrder k ∧ ¬ HasBoundedGaps (restrictedSums A k) := by
  sorry

/--
For $k=2$ the answer is yes, with $b_{n+1}-b_n\leq 2$ for large $n$ [HHP07]: all odd numbers in
$A+A$ are sums of two distinct elements of $A$.
-/
@[category research solved, AMS 11]
theorem erdos_880.variants.two : ∀ A : Set ℕ, A.IsAsymptoticAddBasisOfOrder 2 →
    ∀ᶠ n : ℕ in atTop, Nat.nth (· ∈ restrictedSums A 2) (n + 1) -
      Nat.nth (· ∈ restrictedSums A 2) n ≤ 2 := by
  sorry

end Erdos880
