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

public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Squares in the plane
-/

@[expose] public section

namespace EuclideanGeometry

/-- A square in the plane, given by its centre, a unit vector along one of its sides and its side
length. The other side direction is the counterclockwise quarter-turn of `direction`. -/
structure Square where
  center : ℝ × ℝ
  direction : ℝ × ℝ
  side : ℝ
  side_pos : 0 < side
  direction_unit : direction.1 ^ 2 + direction.2 ^ 2 = 1

/-- The (closed) set of points of a square. -/
def Square.carrier (S : Square) : Set (ℝ × ℝ) :=
  {p | ∃ x y : ℝ, |x| ≤ S.side / 2 ∧ |y| ≤ S.side / 2 ∧
    p = (S.center.1 + x * S.direction.1 - y * S.direction.2,
      S.center.2 + x * S.direction.2 + y * S.direction.1)}

end EuclideanGeometry
