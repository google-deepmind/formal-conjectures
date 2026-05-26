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

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def Matrix.IsHermitian.maxEigenvalue {𝕜 : Type*} [Field 𝕜] [RCLike 𝕜]
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℝ :=
  iSup hA.eigenvalues

/--
Lovász Theta Function (ϑ(G))
The Lovász theta function is defined as:
ϑ(G) = min λ_max(A)
where the minimum is taken over all symmetric matrices A such that:

A_ij = 1 for all i = j (diagonal entries are 1)
A_ij = 0 for all {i,j} ∈ E (entries corresponding to edges are 0)
A is positive semidefinite

Here λ_max(A) denotes the maximum eigenvalue of A.
-/
noncomputable def lovaszThetaFunction
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  sInf {(Matrix.IsHermitian.maxEigenvalue hA) | (A : Matrix α α ℝ) (hA : A.IsHermitian)
      (_ : ∀ i, A i i = 1) (_ : ∀ i j, G.Adj i j → A i j = 0)}

end SimpleGraph
