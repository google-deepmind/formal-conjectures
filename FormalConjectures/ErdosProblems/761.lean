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
# Erdős Problem 761

*Reference:* [erdosproblems.com/761](https://www.erdosproblems.com/761)

The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours
needed to colour the vertices of $G$ such that each colour class induces either
a complete graph or empty graph. The dichromatic number of $G$, denoted by $\delta(G)$,
is the minimum number $k$ of colours required such that, in any orientation of
the edges of $G$, there is a $k$-colouring of the vertices of $G$ such that there
are no monochromatic oriented cycles.

The first question is due to Erdős and Neumann-Lara. The second question is
due to Erdős and Gimbel. A positive answer to the second question implies a
positive answer to the first via the bound mentioned in Problem 760.
-/

open SimpleGraph

namespace Erdos761

/-- An orientation of a simple graph assigns a direction to each edge:
each edge $\{u,v\}$ is oriented as $u \to v$ or $v \to u$ (but not both). -/
def IsOrientation {V : Type*} (G : SimpleGraph V) (D : V → V → Prop) : Prop :=
  (∀ u v, D u v → G.Adj u v) ∧
  (∀ u v, G.Adj u v → D u v ∨ D v u) ∧
  (∀ u v, D u v → ¬D v u)

/-- A colouring $c : V \to \operatorname{Fin}(k)$ is acyclic with respect to an orientation $D$
if there is no monochromatic directed cycle: no vertex can reach itself
via directed edges within its own colour class. -/
def IsAcyclicColouring {V : Type*} (D : V → V → Prop) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k, ∀ v : V, c v = i →
    ¬Relation.TransGen (fun u w => c u = i ∧ c w = i ∧ D u w) v v

/-- The dichromatic number of $G$: the minimum $k$ such that for every orientation
of $G$, there exists an acyclic $k$-colouring. -/
noncomputable def dichromaticNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∀ D : V → V → Prop, IsOrientation G D →
    ∃ c : V → Fin k, IsAcyclicColouring D k c}

/-- A cochromatic colouring: each colour class induces either a complete
subgraph or an independent set. -/
def IsCochromaticColouring {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number $\zeta(G)$: minimum number of colours in a cochromatic
colouring. -/
noncomputable def cochromaticNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromaticColouring G k c}

/--
**Erdős Problem 761, Question 1** (Erdős–Neumann-Lara):

Must a graph with large chromatic number have large dichromatic number?
For every $n$ there exists $m$ such that $\chi(G) \geq m$ implies $\delta(G) \geq n$.
-/
@[category research open, AMS 5]
theorem erdos_761 : answer(sorry) ↔
    (∀ n : ℕ, ∃ m : ℕ, ∀ (s : ℕ) (G : SimpleGraph (Fin s)),
      G.chromaticNumber.toNat ≥ m →
        dichromaticNumber G ≥ n) := by
  sorry

/--
**Erdős Problem 761, Question 2** (Erdős–Gimbel):

Must a graph with large cochromatic number contain a subgraph with large
dichromatic number? For every $n$ there exists $m$ such that $\zeta(G) \geq m$ implies
$G$ contains an induced subgraph with $\delta \geq n$.
-/
@[category research open, AMS 5]
theorem erdos_761.variants.cochromatic : answer(sorry) ↔
    (∀ n : ℕ, ∃ m : ℕ, ∀ (s : ℕ) (G : SimpleGraph (Fin s)),
      cochromaticNumber G ≥ m →
        ∃ (S : Finset (Fin s)),
          dichromaticNumber (G.induce (↑S : Set (Fin s))) ≥ n) := by
  sorry

end Erdos761
