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

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The Gromov product

The Gromov product of `y` and `z` with respect to `x` in a pseudometric space is
`(y, z)_x = (dist x y + dist x z - dist y z) / 2`.

This file is copied from `Mathlib.Topology.MetricSpace.GromovProduct`
(leanprover-community/mathlib4#43641). It is in Mathlib from `v4.34.0`. Delete it when this
repository moves to that version.

## Main definitions

* `Metric.gromovProduct x y z`: the Gromov product of `y` and `z` with respect to `x`.
-/

public section

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] (x y z : X)

/-- The Gromov product of `y` and `z` with respect to `x`. -/
noncomputable def gromovProduct : ℝ := (dist x y + dist x z - dist y z) / 2

lemma gromovProduct_eq : gromovProduct x y z = (dist x y + dist x z - dist y z) / 2 := by rfl

lemma gromovProduct_comm : gromovProduct x y z = gromovProduct x z y := by
  grind [gromovProduct_eq, dist_comm]

grind_pattern gromovProduct_comm => gromovProduct x y z where y =/= z

@[grind! .]
lemma gromovProduct_nonneg : 0 ≤ gromovProduct x y z := by
  grind [gromovProduct_eq, dist_triangle_left y z x]

lemma gromovProduct_le_dist_left : gromovProduct x y z ≤ dist x y := by
  grind [gromovProduct_eq, dist_triangle x y z]

lemma gromovProduct_le_dist_right : gromovProduct x y z ≤ dist x z := by
  grind [gromovProduct_le_dist_left]

@[simp, grind =]
lemma gromovProduct_self_left : gromovProduct x x y = 0 := by
  simp [gromovProduct_eq]

@[simp, grind =]
lemma gromovProduct_self_right : gromovProduct x y x = 0 := by
  simp [gromovProduct_eq, dist_comm]

@[simp]
lemma gromovProduct_self : gromovProduct x y y = dist x y := by
  simp [gromovProduct_eq]

lemma gromovProduct_add_gromovProduct₁₃ : gromovProduct x y z + gromovProduct z y x = dist x z := by
  grind [gromovProduct_eq, dist_comm]

lemma gromovProduct_add_gromovProduct₁₂ : gromovProduct x y z + gromovProduct y x z = dist x y := by
  grind [gromovProduct_eq, dist_comm]

end Metric
