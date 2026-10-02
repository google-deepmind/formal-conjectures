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

public import FormalConjecturesForMathlib.Geometry.Group.WordMetric
public import FormalConjecturesForMathlib.Topology.MetricSpace.Hyperbolic

/-!
# Hyperbolic groups

A finitely generated group is hyperbolic if its induced metric space with respect to a chosen family
of `Group.Generators` satisfies the Gromov hyperbolicity condition.

This is being upstreamed to Mathlib in leanprover-community/mathlib4#44339.

## Main definitions

* `Group.Generators.IsHyperbolicWith`: A group is `δ`-hyperbolic with respect to a generating
  family `P` if its induced metric space is `δ`-hyperbolic.
* `Group.IsHyperbolic`: A group `G` is hyperbolic if there exists a finite generating family `P`
  and a constant `δ` such that `G` is `δ`-hyperbolic with respect to `P`.

## Main results

* `[Group.IsHyperbolic G] : Group.FG G`: Every hyperbolic group is finitely generated.
* `[Finite G] : Group.IsHyperbolic G`: Every finite group is hyperbolic.

## Implementation notes

The hyperbolicity condition applies directly to the word metric, without requiring the Cayley graph.
-/

@[expose] public section

namespace Group

variable {G ι : Type*} [Group G]

/-- A group is `δ`-hyperbolic with respect to a generating family `P` if its induced metric space is
`δ`-hyperbolic. -/
def Generators.IsHyperbolicWith (P : Generators G ι) (δ : ℝ) : Prop :=
  letI := P.normedGroup
  Metric.IsHyperbolicWith G δ

/-- A group `G` is hyperbolic if there exists a finite generating family `P` and a constant `δ` such
that `G` is `δ`-hyperbolic with respect to `P`. -/
class IsHyperbolic (G : Type*) [Group G] : Prop where
  exists_isHyperbolicWith (G) : ∃ (n : ℕ) (P : Generators G (Fin n)) (δ : ℝ), P.IsHyperbolicWith δ

/-- Every hyperbolic group is finitely generated. -/
instance [IsHyperbolic G] : FG G := by
  obtain ⟨_, P, _, _⟩ := IsHyperbolic.exists_isHyperbolicWith G
  exact P.fg

/-- Every finite group is hyperbolic. -/
instance [Finite G] : IsHyperbolic G :=
  let ⟨n, ⟨P⟩⟩ := fg_iff_nonempty_finite_generators.mp inferInstance
  ⟨n, P, Metric.IsHyperbolic.exists_isHyperbolicWith⟩

end Group
