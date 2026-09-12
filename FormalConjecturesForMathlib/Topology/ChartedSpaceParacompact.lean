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

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Compactness.Paracompact

/-!
# Hereditary paracompactness of a compact charted space

A compact Hausdorff charted space whose model is locally compact and second countable is
hereditarily paracompact: every open subset of it is paracompact. This is the input that makes
the sheaf-theoretic comparisons on a compact analytic manifold work on every open subset, not
only on the whole space.
-/

@[expose] public section

universe u

namespace TopologicalSpace

/-- Every open subset of a compact Hausdorff charted space with locally compact,
second-countable model is paracompact. This is the hereditary-paracompactness input used for
compact analytic manifolds. -/
theorem opens_paracompactSpace_of_compact_chartedSpace
    {H M : Type u} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [SecondCountableTopology H] [LocallyCompactSpace H]
    [CompactSpace M] [T2Space M] (U : Opens M) :
    ParacompactSpace U := by
  let : SigmaCompactSpace M := inferInstance
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact H M
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let : SigmaCompactSpace U := inferInstance
  infer_instance

end TopologicalSpace
