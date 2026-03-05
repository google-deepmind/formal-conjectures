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
# Erdős Problem 736

*Reference:* [erdosproblems.com/736](https://www.erdosproblems.com/736)

A conjecture of Walter Taylor. Let $G$ be a graph with chromatic number $\aleph_1$.
Is there, for every cardinal number $m$, some graph $G_m$ of chromatic number $m$
such that every finite subgraph of $G_m$ is a subgraph of $G$?

Komjáth and Shelah [KoSh05] proved that it is consistent that the answer is no,
so the conjecture is not provable in ZFC.

[KoSh05] Komjáth, P. and Shelah, S., _Finite subgraphs of uncountably chromatic
graphs_. J. Graph Theory 49 (2005), 28-38.
-/

open SimpleGraph Cardinal

universe u

namespace Erdos736

/-- $G$ contains a copy of $H$: there is an injective map preserving adjacency. -/
def ContainsCopy {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/-- The cardinal chromatic number of a graph: the infimum of cardinals $\kappa$
for which $G$ admits a proper $\kappa$-coloring. -/
noncomputable def cardChromaticNumber {V : Type u}
    (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (α : Type u), #α = κ ∧ Nonempty (G.Coloring α)}

/--
Erdős Problem 736 [Er81] [Er93, p. 343]:

If $G$ is a graph with chromatic number $\aleph_1$, then for every cardinal $m$,
there exists a graph $G_m$ with chromatic number $m$ such that every finite
subgraph of $G_m$ is also a subgraph of $G$.

A conjecture of Walter Taylor. Komjáth and Shelah [KoSh05] proved that
this is consistently false (not provable in ZFC).
-/
@[category research open, AMS 3 5]
theorem erdos_736 : answer(sorry) ↔
    ∀ (V : Type u) (G : SimpleGraph V),
    cardChromaticNumber G = aleph 1 →
    ∀ (m : Cardinal.{u}),
    ∃ (W : Type u) (Gm : SimpleGraph W),
      cardChromaticNumber Gm = m ∧
      ∀ (U : Type u) [Fintype U] (H : SimpleGraph U),
        ContainsCopy Gm H → ContainsCopy G H := by
  sorry

end Erdos736
