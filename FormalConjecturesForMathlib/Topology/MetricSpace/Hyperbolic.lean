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
/- Original Mathlib authors: Hang Lu Su, Katerina Hristova. -/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import FormalConjecturesForMathlib.Topology.MetricSpace.GromovProduct

/-!
# Gromov hyperbolic pseudometric spaces

This is being upstreamed to Mathlib in leanprover-community/mathlib4#43723.

TODO: delete this file when this repository moves to a Mathlib version that contains it.

## Main definitions

* `Metric.IsHyperbolicWith`: A pseudometric space is hyperbolic with constant `δ`
  if and only if for all `w x y z` the four-point condition
  `min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z` holds.
* `Metric.IsHyperbolic`: A pseudometric space is hyperbolic if it is `δ`-hyperbolic for some
  constant `δ`.

## Main results

* `Metric.isHyperbolicWith_diam_univ`: A bounded space is `δ`-hyperbolic with respect to its
  diameter.

## Implementation notes

The constant `δ` in `IsHyperbolicWith X δ` is a real number. For a non-empty space,
taking `w = x = y = z` in the four-point condition yields `0 ≤ δ`.
-/

@[expose] public section

namespace Metric

/-! ### δ-hyperbolic spaces -/

/-- A pseudometric space is `δ`-hyperbolic if for all `w x y z` the four-point condition
`min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z` holds. -/
def IsHyperbolicWith (X : Type*) [PseudoMetricSpace X] (δ : ℝ) : Prop :=
  ∀ w x y z : X, min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z

variable {X : Type*} [PseudoMetricSpace X]

/-- A pseudometric space with all distances bounded above by `k` is `k`-hyperbolic. -/
@[grind .]
lemma isHyperbolicWith_of_forall_dist_le {k : ℝ} (hk : ∀ x y : X, dist x y ≤ k) :
    IsHyperbolicWith X k := by
  grind [IsHyperbolicWith, gromovProduct_le_dist_left]

/-- A bounded space is `δ`-hyperbolic with respect to its diameter. -/
theorem isHyperbolicWith_diam_univ [BoundedSpace X] :
    IsHyperbolicWith X (diam (Set.univ : Set X)) := by
  grind [dist_le_diam_of_mem, Bornology.isBounded_univ]

/-! ### Hyperbolic spaces -/

/-- A pseudometric space is hyperbolic if it is `δ`-hyperbolic for some real constant `δ`. -/
class IsHyperbolic (X : Type*) [PseudoMetricSpace X] : Prop where
  exists_isHyperbolicWith : ∃ δ, IsHyperbolicWith X δ

/-- Every bounded pseudometric space is hyperbolic. -/
instance [BoundedSpace X] : IsHyperbolic X := ⟨_, isHyperbolicWith_diam_univ⟩

end Metric
