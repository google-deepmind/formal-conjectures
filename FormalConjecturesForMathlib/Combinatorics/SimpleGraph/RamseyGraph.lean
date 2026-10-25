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

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Ramsey graphs
-/

@[expose] public section

namespace SimpleGraph

open Real

/-- `G` contains no clique or independent set on `C log n` vertices. -/
def IsRamseyGraph {n : ℕ} (C : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
    (S.card : ℝ) < C * log n

end SimpleGraph
