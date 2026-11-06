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
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-!
# Heterogeneous clique Ramsey numbers
-/

@[expose] public section

namespace SimpleGraph

/-- The heterogeneous multicolour Ramsey number with a clique target for each colour. -/
noncomputable def cliqueRamseyNumber {ι : Type*} (target : ι → ℕ) : ℕ :=
  sInf {m | ∀ C : TopEdgeLabeling (Fin m) ι, ∃ i, ¬ (C.labelGraph i).CliqueFree (target i)}

end SimpleGraph
