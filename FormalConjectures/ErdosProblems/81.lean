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
# Erdős Problem 81

*Reference:* [erdosproblems.com/81](https://www.erdosproblems.com/81)

Can the edges of a chordal graph on $n$ vertices be partitioned into at most
$n^2/6 + O(n)$ cliques?

[EOZ93] Erdős, P., Ordman, E.T., and Zalcstein, Y., *Clique partitions of chordal graphs*,
Combinatorics, Probability and Computing **2** (1993), 409-415.
-/

open SimpleGraph

namespace Erdos81

/--
An induced cycle of length $k$ in a simple graph $G$: an injective map
$f : \text{Fin}\ k \to V$ such that $f(i)$ and $f(j)$ are adjacent if and only if
$i$ and $j$ are consecutive modulo $k$. This captures the notion that $f$ traces out a
cycle with no chords.
-/
def HasInducedCycle {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : Fin k → V, Function.Injective f ∧
    ∀ i j : Fin k, i ≠ j →
      (G.Adj (f i) (f j) ↔ (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val)

/--
A graph is chordal if it contains no induced cycle of length $\geq 4$.
Equivalently, every cycle of length $\geq 4$ has a chord.
-/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, 4 ≤ k → ¬HasInducedCycle G k

/--
Erdős Problem 81 (Erdős, Ordman, Zalcstein [EOZ93]):

Let $G$ be a chordal graph on $n$ vertices — that is, $G$ has no induced cycles of
length greater than 3. Can the edges of $G$ be partitioned into $n^2/6 + O(n)$
many cliques?

The example of all edges between a complete graph on $n/3$ vertices and an empty
graph on $2n/3$ vertices shows that $n^2/6 + O(n)$ is sometimes necessary.

Formalized as: there exists a constant $C > 0$ such that for all $n$ and all
chordal graphs $G$ on $n$ vertices, there exists a collection $P$ of cliques
(vertex sets, each pairwise adjacent in $G$) that partition the edges of $G$,
with $|P| \leq n^2/6 + Cn$.
-/
@[category research open, AMS 5]
theorem erdos_81 : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      IsChordal G →
      ∃ P : Finset (Finset (Fin n)),
        -- Each set in P is a clique in G
        (∀ S ∈ P, G.IsClique (↑S : Set (Fin n))) ∧
        -- Every edge of G is covered by some clique in P
        (∀ u v : Fin n, G.Adj u v → ∃ S ∈ P, u ∈ S ∧ v ∈ S) ∧
        -- No edge belongs to two distinct cliques (partition, not just cover)
        (∀ S₁ ∈ P, ∀ S₂ ∈ P, S₁ ≠ S₂ →
          ∀ u v : Fin n, u ∈ S₁ → v ∈ S₁ → u ∈ S₂ → v ∈ S₂ → ¬G.Adj u v) ∧
        -- The number of cliques is at most n²/6 + C·n
        (P.card : ℝ) ≤ (n : ℝ) ^ 2 / 6 + C * (n : ℝ) := by
  sorry

end Erdos81
