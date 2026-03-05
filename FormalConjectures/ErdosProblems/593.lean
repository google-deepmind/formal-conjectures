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
# Erdős Problem 593

*Reference:* [erdosproblems.com/593](https://www.erdosproblems.com/593)

Characterize those finite $3$-uniform hypergraphs which appear in every
$3$-uniform hypergraph of chromatic number $> \aleph_0$.

Similar problems were investigated by Erdős, Galvin, and Hajnal [EGH75].
Erdős claims that for graphs the problem is completely solved: a graph of
chromatic number $\geq \aleph_1$ must contain all finite bipartite graphs but need not
contain any fixed odd cycle.

We define a finite $3$-uniform hypergraph $F$ to be *obligatory* if it appears
in every $3$-uniform hypergraph of uncountable chromatic number. By analogy
with the graph case, we conjecture that the obligatory finite $3$-uniform
hypergraphs are exactly the $2$-colorable ones.

[EGH75] Erdős, P., Galvin, F., and Hajnal, A.

[Er95d] Erdős, P.
-/

namespace Erdos593

/-- A $3$-uniform hypergraph on vertex type $V$: a collection of $3$-element
    subsets of $V$. -/
structure Hypergraph3 (V : Type*) where
  edges : Set (Finset V)
  uniform : ∀ e ∈ edges, e.card = 3

/-- A proper coloring of a $3$-uniform hypergraph: no edge is monochromatic
    (every edge contains two vertices receiving different colors). -/
def Hypergraph3.IsProperColoring {V : Type*} (H : Hypergraph3 V)
    {C : Type*} (c : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- A $3$-uniform hypergraph has uncountable chromatic number: it admits no
    proper coloring with countably many colors. -/
def Hypergraph3.HasUncountableChromaticNumber {V : Type*}
    (H : Hypergraph3 V) : Prop :=
  ∀ (C : Type*) [Countable C], ¬∃ c : V → C, H.IsProperColoring c

/-- A finite $3$-uniform hypergraph $F$ on $W$ embeds into $H$ on $V$: there is an
    injective map from $W$ to $V$ sending every edge of $F$ to an edge of $H$. -/
def Hypergraph3.ContainsCopy {V W : Type*}
    (H : Hypergraph3 V) (F : Hypergraph3 W) : Prop :=
  ∃ f : W ↪ V, ∀ e ∈ F.edges, e.map f ∈ H.edges

/-- A $3$-uniform hypergraph is $2$-colorable: it admits a proper coloring with
    two colors such that no edge is monochromatic. -/
def Hypergraph3.Is2Colorable {V : Type*} (H : Hypergraph3 V) : Prop :=
  ∃ c : V → Bool, H.IsProperColoring c

/--
Erdős Problem 593 [Er95d]:

A finite $3$-uniform hypergraph appears in every $3$-uniform hypergraph of
uncountable chromatic number if and only if it is $2$-colorable.

This is conjectured by analogy with the known graph result: a graph of
chromatic number $\geq \aleph_1$ must contain all finite bipartite graphs but need not
contain any fixed odd cycle [EGH75].
-/
@[category research open, AMS 5]
theorem erdos_593 (W : Type*) [Fintype W]
    (F : Hypergraph3 W) :
    (∀ (V : Type*) (H : Hypergraph3 V),
      H.HasUncountableChromaticNumber → H.ContainsCopy F) ↔
    F.Is2Colorable := by
  sorry

end Erdos593
