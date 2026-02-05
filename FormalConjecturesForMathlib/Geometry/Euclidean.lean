/-
Copyright 2025 The Formal Conjectures Authors.

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

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

/-
A set of points is in general position if no three points are collinear.
-/
def GeneralPosition
    {R : Type*} {V P : Type*}
    [DivisionRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]
    (S : Set P) : Prop :=
  ∀ s : Set P, s ⊆ S → s.ncard = 3 → ¬ Collinear R s
