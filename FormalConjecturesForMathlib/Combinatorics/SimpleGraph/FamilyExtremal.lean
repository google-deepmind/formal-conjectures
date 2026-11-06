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

public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Extremal numbers of finite graph families
-/

@[expose] public section

namespace SimpleGraph

/-- A finite graph, bundled with its vertex count, so that a family may mix orders. -/
structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

/-- A host graph is `family`-free when it contains no member of `family` as a subgraph. -/
def FamilyFree (family : Finset FiniteGraph) {n : ℕ} (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

open scoped Classical in
/-- $\mathrm{ex}(n;\mathcal{F})$, the greatest number of edges of a graph on `n` vertices
containing no member of `family`. The value is zero if no graph is admissible. -/
noncomputable def familyExtremalNumber (family : Finset FiniteGraph) (n : ℕ) : ℕ :=
  (Finset.univ.filter (FamilyFree family)).sup
    fun host : SimpleGraph (Fin n) => host.edgeFinset.card

end SimpleGraph
