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
# Erdős Problem 903

*References:*
- [erdosproblems.com/903](https://www.erdosproblems.com/903)
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*. (1982),
  59-79.
- [dBEr48] de Bruijn, N. G. and Erdős, P., *On a combinatorial problem*. Nederl. Akad. Wetensch.,
  Proc. (1948), 1277-1279.
- [EFSW85] Erdős, P. and Fowler, Joel C. and Sós, Vera T. and Wilson, Richard M.,
  *On $2$-designs*. J. Combin. Theory Ser. A (1985), 131-142.
-/

@[expose] public section

namespace Erdos903

/--
A family of blocks `A 0, …, A (t - 1)` of `{0, …, n - 1}` is a *block design* (pairwise balanced
design) if every block has at least two points and every pair of distinct points is contained in
exactly one block.
-/
def IsBlockDesign {n t : ℕ} (A : Fin t → Finset (Fin n)) : Prop :=
  (∀ i, 2 ≤ (A i).card) ∧ ∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i

/--
Let $n=p^2+p+1$ for some prime power $p$, and let $A_1,\ldots,A_t\subseteq \{1,\ldots,n\}$ be a
block design (so that every pair $x,y\in \{1,\ldots,n\}$ is contained in exactly one $A_i$).

Is it true that if $t>n$ then $t\geq n+p$?

A conjecture of Erdős and Sós. The classic finite geometry construction shows that $t=n$ is
possible. A theorem of Erdős and de Bruijn [dBEr48] states that $t\geq n$.

This is true, and was proved by Erdős, Fowler, Sós, and Wilson [EFSW85], who further show that
unless the block design is obtained from a projective plane by 'breaking up' one of its lines then
$t\geq n+cp$ where $c\approx 1.148$.

In general, one can ask what the possible values of $t$ are, for a given $n$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos903.lean#L1540"]
theorem erdos_903 : answer(True) ↔ ∀ p : ℕ, IsPrimePow p →
    ∀ (t : ℕ) (A : Fin t → Finset (Fin (p ^ 2 + p + 1))), IsBlockDesign A →
      p ^ 2 + p + 1 < t → p ^ 2 + p + 1 + p ≤ t := by
  sorry

/-- The statement holds for every $p \geq 2$, not just prime powers. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos903.lean#L1522"]
theorem erdos_903.variants.general : ∀ p : ℕ, 2 ≤ p →
    ∀ (t : ℕ) (A : Fin t → Finset (Fin (p ^ 2 + p + 1))), IsBlockDesign A →
      p ^ 2 + p + 1 < t → p ^ 2 + p + 1 + p ≤ t := by
  sorry

/--
A theorem of Erdős and de Bruijn [dBEr48] states that a block design on $n$ points in which no
block contains all the points has $t\geq n$ blocks.
-/
@[category research solved, AMS 5]
theorem erdos_903.variants.de_bruijn_erdos : ∀ (n t : ℕ) (A : Fin t → Finset (Fin n)), 2 ≤ n →
    IsBlockDesign A → (∀ i, (A i).card < n) → n ≤ t := by
  sorry

end Erdos903
