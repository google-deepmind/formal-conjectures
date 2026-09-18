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
public import FormalConjecturesForMathlib.Analysis.Matrix.Spectrum

@[expose] public section

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]
/--
Lovász Theta Function ($\vartheta(G)$).
The Lovász theta function is defined as:
$$\vartheta(G) = \min \lambda_{\max}(A)$$
where the minimum is taken over all real symmetric (Hermitian) matrices $A$ such that:

* $A_{ii} = 1$ for all $i$ (diagonal entries are $1$), and
* $A_{ij} = 1$ for all $\{i,j\} \notin E(G)$ (entries corresponding to non-edges are $1$).

Here $\lambda_{\max}(A)$ denotes the maximum eigenvalue of $A$.
-/
noncomputable def lovaszThetaFunction
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  sInf {(Matrix.IsHermitian.maxEigenvalue hA) | (A : Matrix α α ℝ) (hA : A.IsHermitian)
      (_ : ∀ i, A i i = 1) (_ : ∀ i j, ¬G.Adj i j → A i j = 1)}

end SimpleGraph
