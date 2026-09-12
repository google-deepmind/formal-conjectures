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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Minor

@[expose] public section

/-!
# Planarity of a finite simple graph (Wagner's characterization)

Mathlib has no planarity predicate (as of 2026). For finite graphs we define
planarity via **Wagner's theorem** as the *definition*: a finite graph is planar
iff it has neither `K₅` nor `K₃,₃` as a minor. This is built on the graph-minor
relation `SimpleGraph.IsMinor` (branch sets).

*Reference:* K. Wagner, *Über eine Eigenschaft der ebenen Komplexe*, Math. Ann.
114 (1937), 570–590.
-/

namespace SimpleGraph

variable {V : Type*}

/-- `G` has a `Kₙ` (complete graph on `n` vertices) minor. -/
def HasKMinor (G : SimpleGraph V) (n : ℕ) : Prop :=
  (⊤ : SimpleGraph (Fin n)).IsMinor G

/-- `G` has a `K_{m,n}` (complete bipartite graph) minor. -/
def HasKmnMinor (G : SimpleGraph V) (m n : ℕ) : Prop :=
  (completeBipartiteGraph (Fin m) (Fin n)).IsMinor G

/-- **Combinatorial (Wagner) planarity.** A finite graph is *planar* iff it
contains neither `K₅` nor `K₃,₃` as a minor. Since Mathlib has no native planarity
predicate, we take Wagner's theorem as the definition. -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  ¬ HasKMinor G 5 ∧ ¬ HasKmnMinor G 3 3

end SimpleGraph
