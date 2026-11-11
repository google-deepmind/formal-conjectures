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

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Uniform finite random graphs
-/

@[expose] public section

namespace SimpleGraph

open scoped Classical in
/-- The proportion of (labelled) graphs on `n` vertices satisfying `P`. A property holds for
*almost all graphs* if this proportion tends to `1`. -/
noncomputable def uniformGraphProportion (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) (n : ℕ) : ℝ :=
  ((Finset.univ.filter (P n)).card : ℝ) / Fintype.card (SimpleGraph (Fin n))

open scoped Classical in
/-- The probability that the random graph `G(n, m)`, chosen uniformly among the labelled graphs
on `n` vertices with exactly `m` edges, satisfies `P`. -/
noncomputable def fixedEdgeGraphProbability (n m : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((Finset.univ.filter fun G : SimpleGraph (Fin n) ↦ G.edgeFinset.card = m ∧ P G).card : ℝ) /
    (Finset.univ.filter fun G : SimpleGraph (Fin n) ↦ G.edgeFinset.card = m).card

/-- A sequence of properties holds almost surely for uniformly chosen labelled graphs. -/
def AlmostSurely (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Prop :=
  Filter.Tendsto (uniformGraphProportion P) Filter.atTop (nhds 1)

end SimpleGraph
