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
# Erdős Problem 72

*References:*
- [erdosproblems.com/72](https://www.erdosproblems.com/72)
- [Er94b] Erdős, Paul, *Some problems in number theory, combinatorics and combinatorial geometry*.
  Math. Pannon. (1994), 261-269.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97b] Erdős, Paul, *Some old and new problems in various branches of combinatorics*. Discrete
  Math. (1997), 227-231.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul
  Erdős, I (1997), 47-67.
- [Bo77] Bollobás, Béla, *Cycles modulo $k$*. Bull. London Math. Soc. (1977), 97-98.
- [Ve05] Verstraete, Jacques, *Unavoidable cycle lengths in graphs*. J. Graph Theory (2005),
  151-167.
- [LiMo20] Liu, Hong and Montgomery, Richard, *A solution to Erdős and Hajnal's odd cycle
  problem*. arXiv:2010.15802 (2020).
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos72

open scoped Classical in
/--
Is there a set $A\subset \mathbb{N}$ of density $0$ and a constant $c>0$ such that every graph on
sufficiently many vertices with average degree $\geq c$ contains a cycle whose length is in $A$?

Bollobás [Bo77] proved that such a $c$ does exist if $A$ is an infinite arithmetic progression
containing even numbers (see [71](https://www.erdosproblems.com/71)).

Erdős was 'almost certain' that if $A$ is the set of powers of $2$ then no such $c$ exists
(although he conjectured that $n$ vertices and average degree $\gg (\log n)^{C}$ suffices for
some $C=O(1)$). If $A$ is the set of squares (or the set of $p\pm 1$ for $p$ prime) then he had
no guess.

Solved by Verstraëte [Ve05], who gave a non-constructive proof that such a set $A$ exists.

Liu and Montgomery [LiMo20] proved that in fact this is true when $A$ is the set of powers of $2$
(more generally any set of even numbers which doesn't grow too quickly) - in particular this
contradicts the previous belief of Erdős.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos72.lean#L184"]
theorem erdos_72 : answer(True) ↔ ∃ A : Set ℕ, A.HasDensity 0 ∧ ∃ c : ℚ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), c ≤ G.averageDegree →
      ∃ (v : Fin n) (w : G.Walk v v), w.IsCycle ∧ w.length ∈ A := by
  sorry

open scoped Classical in
/--
Liu and Montgomery [LiMo20] proved that there is a constant $c > 0$ such that every graph on
sufficiently many vertices with average degree $\geq c$ contains a cycle whose length is a power
of $2$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos72.lean#L157"]
theorem erdos_72.variants.powers_of_two : ∃ c : ℚ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), c ≤ G.averageDegree →
      ∃ (v : Fin n) (w : G.Walk v v), w.IsCycle ∧ ∃ k : ℕ, w.length = 2 ^ k := by
  sorry

end Erdos72
