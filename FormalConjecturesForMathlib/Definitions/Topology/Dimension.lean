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

public import Mathlib.Topology.KrullDimension

import FormalConjecturesForMathlib.Mathlib.Topology.KrullDimension

/-!
# The dimension of an irreducible topological space
-/

public noncomputable section

namespace TopologicalSpace

/-- The dimension of an irreducible topological space is its Krull dimension: the supremum of the
lengths of chains of irreducible closed subsets.

Truncating to `ℕ` collapses the two degenerate values of `topologicalKrullDim`: the empty space,
which the `IrreducibleSpace` hypothesis rules out, and infinite-dimensional spaces, which come out
as `0`. Irreducibility also makes this *the* dimension of the space, rather than the maximum of the
dimensions of its irreducible components. -/
@[expose, nolint unusedArguments]
def dim (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] : ℕ :=
  ((topologicalKrullDim X).unbotD 0).toNat

end TopologicalSpace
