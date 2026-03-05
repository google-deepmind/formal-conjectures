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
# Erdős Problem 638

Is it true that for every infinite cardinal $\kappa$ there is a graph $G$ such that every
finite induced subgraph of $G$ belongs to a given family $S$ with the Ramsey property, and
every $\kappa$-colouring of the edges of $G$ contains a monochromatic triangle?

*Reference:* [erdosproblems.com/638](https://www.erdosproblems.com/638)
-/

open SimpleGraph Cardinal

namespace Erdos638

/-- A symmetric colouring of a simple graph has a **monochromatic triangle**
    if three pairwise-adjacent vertices have all three edges the same colour. -/
def HasMonoTriangle {V : Type*} (G : SimpleGraph V) {α : Type*}
    (c : V → V → α) : Prop :=
  ∃ a b d : V, G.Adj a b ∧ G.Adj b d ∧ G.Adj a d ∧
    c a b = c b d ∧ c a b = c a d

/-- The induced subgraph of $G$ pulled back along an embedding
    $f : \operatorname{Fin} m \hookrightarrow V$. -/
def inducedFinSubgraph {V : Type*} (G : SimpleGraph V) {m : ℕ}
    (f : Fin m ↪ V) : SimpleGraph (Fin m) where
  Adj i j := G.Adj (f i) (f j)
  symm _ _ h := G.symm h
  loopless i h := G.loopless (f i) h

/-- Two graphs on $\operatorname{Fin} m$ are isomorphic via a permutation of vertices. -/
def FinGraphIso {m : ℕ} (G H : SimpleGraph (Fin m)) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), ∀ i j, G.Adj i j ↔ H.Adj (σ i) (σ j)

/--
**Erdős Problem 638**

Let $S$ be a family of finite graphs (indexed by vertex count) with the Ramsey
property: for every $n \geq 1$, some member of $S$ forces a monochromatic triangle
under any $n$-colouring of its edges.

Is it true that for every infinite cardinal $\kappa$, there exists a graph $G$ such that
every finite induced subgraph of $G$ belongs (up to isomorphism) to $S$, and
every $\kappa$-colouring of the edges of $G$ contains a monochromatic triangle?
-/
@[category research open, AMS 5]
theorem erdos_638 : answer(sorry) ↔
    ∀ (S : (m : ℕ) → Set (SimpleGraph (Fin m)))
      (_ : ∀ n : ℕ, n ≥ 1 →
        ∃ m : ℕ, ∃ G ∈ S m,
          ∀ (c : Fin m → Fin m → Fin n), (∀ u v, c u v = c v u) →
            HasMonoTriangle G c)
      (κ : Cardinal) (_ : ℵ₀ ≤ κ),
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ (m : ℕ) (f : Fin m ↪ V),
        ∃ H ∈ S m, FinGraphIso (inducedFinSubgraph G f) H) ∧
      ∀ (α : Type) (_ : #α = κ) (c : V → V → α),
        (∀ u v, c u v = c v u) → HasMonoTriangle G c := by
  sorry

end Erdos638
