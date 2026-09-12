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

import FormalConjecturesUtil

/-!
# Erdős Problem 1018

*References:*
- [erdosproblems.com/1018](https://www.erdosproblems.com/1018)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [KoPy88] Kostochka, A. and Pyber, L., *Small topological complete subgraphs of ``dense'' graphs*.
  Combinatorica (1988), 83--86.
-/

open Filter SimpleGraph

namespace SimpleGraph

/--
`ContainsSubdivision H G` means `G` contains a subdivision of `H`: the vertices of `H` inject into
those of `G`, and each edge of `H` is realized by a path whose internal vertices avoid the image of
that injection and are pairwise disjoint across distinct undirected edges.

Mathlib has no graph-minor or subdivision API. This is the usual topological-minor formulation of
Kuratowski's criterion.
-/
def ContainsSubdivision {α β : Type*} (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ∃ (f : α ↪ β) (P : ∀ (x y : α), H.Adj x y → G.Walk (f x) (f y)),
    (∀ {x y : α} (h : H.Adj x y), (P x y h).IsPath) ∧
    (∀ {x y : α} (h : H.Adj x y) (a : α), f a ∉ (P x y h).support.tail.dropLast) ∧
    (∀ {x y x' y' : α} (h : H.Adj x y) (h' : H.Adj x' y'),
      s(x, y) ≠ s(x', y') →
        ∀ v ∈ (P x y h).support.tail.dropLast, v ∉ (P x' y' h').support.tail.dropLast)

/--
A simple graph is planar iff it contains no subdivision of `K₅` or `K_{3,3}` (Kuratowski).
-/
def Planar {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ ContainsSubdivision (completeGraph (Fin 5)) G ∧
    ¬ ContainsSubdivision (completeBipartiteGraph (Fin 3) (Fin 3)) G

end SimpleGraph

namespace Erdos1018

open scoped Classical in
/--
Let $\epsilon>0$. Is there a constant $C_\epsilon$ such that, for all large $n$, every graph on
$n$ vertices with at least $n^{1+\epsilon}$ edges must contain a subgraph on at most $C_\epsilon$
vertices which is non-planar?

Erdős [Er71] writes it is 'not difficult to see' that $C_\epsilon\to \infty$ as $\epsilon\to 0$.

This was solved in the affirmative by Kostochka and Pyber [KoPy88], who proved that $G$ must
contain a subdivision of $K_5$ (which is non-planar) with $O_\epsilon(1)$ many vertices.
-/
@[category research solved, AMS 5]
theorem erdos_1018 : answer(True) ↔
    ∀ ε > (0 : ℝ), ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        (n : ℝ) ^ (1 + ε) ≤ (G.edgeFinset.card : ℝ) →
          ∃ s : Finset (Fin n), s.card ≤ C ∧ ¬ (G.induce s).Planar := by
  sorry

open scoped Classical in
/--
This was solved in the affirmative by Kostochka and Pyber [KoPy88], who proved that $G$ must
contain a subdivision of $K_5$ (which is non-planar) with $O_\epsilon(1)$ many vertices.
-/
@[category research solved, AMS 5]
theorem erdos_1018.variants.kostochka_pyber :
    ∀ ε > (0 : ℝ), ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        (n : ℝ) ^ (1 + ε) ≤ (G.edgeFinset.card : ℝ) →
          ∃ s : Finset (Fin n), s.card ≤ C ∧
            ContainsSubdivision (completeGraph (Fin 5)) (G.induce s) := by
  sorry

open scoped Classical in
/--
Erdős [Er71] writes it is 'not difficult to see' that $C_\epsilon\to \infty$ as $\epsilon\to 0$.
-/
@[category research solved, AMS 5]
theorem erdos_1018.variants.constant_unbounded :
    ∀ M : ℕ, ∃ ε > (0 : ℝ), ∃ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n),
        (n : ℝ) ^ (1 + ε) ≤ (G.edgeFinset.card : ℝ) ∧
          ∀ s : Finset (Fin n), s.card ≤ M → (G.induce s).Planar := by
  sorry

end Erdos1018
