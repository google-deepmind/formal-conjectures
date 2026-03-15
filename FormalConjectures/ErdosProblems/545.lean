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
# Erdős Problem 545

*Reference:* [erdosproblems.com/545](https://www.erdosproblems.com/545)

Let $G$ be a graph with $m$ edges and no isolated vertices. Is the Ramsey number $R(G)$
maximised when $G$ is 'as complete as possible'? That is, if $m = \binom{n}{2} + t$ edges
with $0 \leq t < n$ then is $R(G) \leq R(H)$, where $H$ is the graph formed by connecting a
new vertex to $t$ of the vertices of $K_n$?

A question of Erdős and Graham [ErGr75, p.526] [Er84b, p.11].

The weaker question of whether $R(G) \leq 2^{O(\sqrt{m})}$ is Problem 546, proved by
Sudakov [Su11]. Known counterexamples to the literal statement exist for small $m$
($2 \leq m \leq 5$ and $7 \leq m \leq 9$).

[ErGr75] Erdős, P. and Graham, R., _On partition theorems for finite graphs_.
Infinite and finite sets (Colloq., Keszthely, 1973; dedicated to P. Erdős on his 60th birthday),
Vol. I; Colloq. Math. Soc. János Bolyai, Vol. 10, North-Holland, Amsterdam, 1975, pp. 515–527.

[Er84b] Erdős, P., _On some problems in graph theory, combinatorial analysis and
combinatorial number theory_. Graph theory and combinatorics (Cambridge, 1983),
Academic Press, London (1984), 1-17.

[Su11] Sudakov, B., _A conjecture of Erdős on graph Ramsey numbers_. Advances in
Mathematics 227 (2011), 601-609.
-/

open SimpleGraph

namespace Erdos545

/-- A graph $H$ contains a copy of graph $G$ (as a subgraph) if there is an injective
function from $V(G)$ to $V(H)$ that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The diagonal Ramsey number $R(G)$ for a graph $G$ on $\operatorname{Fin}(k)$: the minimum
$N$ such that every graph $H$ on $N$ vertices contains a copy of $G$ or its complement
contains a copy of $G$. -/
noncomputable def ramseyNumber {k : ℕ} (G : SimpleGraph (Fin k)) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G H ∨ ContainsSubgraphCopy G Hᶜ}

/-- The "as complete as possible" graph with $\binom{n}{2} + t$ edges on $n + 1$ vertices.
The first $n$ vertices form $K_n$, and the last vertex is adjacent to the
first $t$ of $K_n$'s vertices. -/
def asCompleteAsPossible (n t : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj u v :=
    u ≠ v ∧ ((u.val < n ∧ v.val < n) ∨
             (u.val = n ∧ v.val < t) ∨
             (v.val = n ∧ u.val < t))
  symm u v := by
    rintro ⟨hne, h | h | h⟩
    · exact ⟨hne.symm, Or.inl ⟨h.2, h.1⟩⟩
    · exact ⟨hne.symm, Or.inr (Or.inr h)⟩
    · exact ⟨hne.symm, Or.inr (Or.inl h)⟩
  loopless u h := h.1 rfl

/--
Erdős Problem 545 [ErGr75, Er84b]:

Let $G$ be a graph with $m$ edges and no isolated vertices. Is the Ramsey number
$R(G)$ maximised when $G$ is 'as complete as possible'? That is, if
$m = \binom{n}{2} + t$ edges with $0 \leq t < n$ then is $R(G) \leq R(H)$, where $H$
is the graph formed by connecting a new vertex to $t$ of the vertices of $K_n$?
-/
@[category research open, AMS 5]
theorem erdos_545 : answer(sorry) ↔ ∀ (n t k : ℕ), t < n →
    ∀ (G : SimpleGraph (Fin k)),
    G.edgeSet.ncard = n.choose 2 + t →
    (∀ v : Fin k, ∃ w : Fin k, G.Adj v w) →
    ramseyNumber G ≤ ramseyNumber (asCompleteAsPossible n t) := by
  sorry

end Erdos545
