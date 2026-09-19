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
# Erdős Problem 664

*References:*
- [erdosproblems.com/664](https://www.erdosproblems.com/664)
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25-42.
- [Er97f] Erdős, Paul, _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
-/

@[expose] public section

open Filter Real Finset

namespace Erdos664

/--
Let $c<1$ be some constant and $A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ be such that
$\lvert A_i\rvert >c\sqrt{n}$ for all $i$ and $\lvert A_i\cap A_j\rvert\leq 1$ for all $i\neq j$.

Must there exist some set $B$ such that $B\cap A_i\neq \emptyset$ and
$\lvert B\cap A_i\rvert \ll_c 1$ for all $i$?

The answer is no, proved by Alon: if $q$ is a large prime power and $n=m=q^2+q+1$ then there
exist $A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ such that
$\lvert A_i\rvert \geq \tfrac{2}{5}\sqrt{n}$ for all $i$ and $\lvert A_i\cap A_j\rvert\leq 1$ for
all $i\neq j$, and yet if $B$ has non-empty intersection with all $A_i$ then there exists $A_j$
such that $\lvert B\cap A_j\rvert \gg \log n$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos664.lean#L214"]
theorem erdos_664 : answer(False) ↔
    ∀ c : ℝ, 0 < c → c < 1 → ∃ K : ℕ, ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      (∀ i, c * √n < (A i).card) → (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, (B ∩ A i).card ≤ K := by
  sorry

/-- Alon's counterexample already works for $c=2/5$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos664.lean#L214"]
theorem erdos_664.variants.two_fifths :
    ¬ ∃ K : ℕ, ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      (∀ i, 2 / 5 * √n < (A i).card) → (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, (B ∩ A i).card ≤ K := by
  sorry

/--
In [Er81] the condition $\lvert A_i\cap A_j\rvert\leq 1$ for all $i\neq j$ is replaced by every
two points in $\{1,\ldots,n\}$ being contained in exactly one $A_i$, that is,
$A_1,\ldots,A_m$ is a pairwise balanced block design (and the condition $c<1$ is omitted). This
weaker version remains open, although Alon conjectures the answer there to also be no.
-/
@[category research open, AMS 5]
theorem erdos_664.variants.block_design : answer(sorry) ↔
    ∃ K : ℕ, ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, (B ∩ A i).card ≤ K := by
  sorry

end Erdos664
