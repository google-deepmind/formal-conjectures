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

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The distance matrix of a graph

The distance matrix of a graph $G$ has entry $\operatorname{dist}(u, v)$ at $(u, v)$. Mathlib's
`SimpleGraph.dist` is $0$ when no path joins $u$ and $v$.
-/

@[expose] public section

namespace SimpleGraph

variable {α : Type*}

/-- The distance matrix of `G`, with real entries `G.dist u v`. -/
noncomputable def distanceMatrix (G : SimpleGraph α) : Matrix α α ℝ :=
  Matrix.of fun u v => (G.dist u v : ℝ)

@[simp]
lemma distanceMatrix_apply (G : SimpleGraph α) (u v : α) :
    G.distanceMatrix u v = G.dist u v :=
  rfl

lemma isSymm_distanceMatrix (G : SimpleGraph α) : G.distanceMatrix.IsSymm := by
  ext u v
  simp [distanceMatrix, dist_comm]

end SimpleGraph
