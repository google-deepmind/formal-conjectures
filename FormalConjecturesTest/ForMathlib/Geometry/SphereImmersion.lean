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

public import FormalConjecturesForMathlib.Geometry.SphereImmersion

/-!
# Sanity checks for the canonical sphere normal

The canonical normal of the standard inclusion is checked explicitly at the six signed coordinate
axes of the unit sphere.
-/

@[expose] public section

open Metric
open scoped EuclideanGeometry

namespace SphereImmersionTest

open EuclideanHypersurface

private def positiveAxis0 : sphere (0 : ℝ³) 1 :=
  ⟨!₂[1, 0, 0], by
    norm_num [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

private def negativeAxis0 : sphere (0 : ℝ³) 1 :=
  ⟨!₂[-1, 0, 0], by
    norm_num [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

private def positiveAxis1 : sphere (0 : ℝ³) 1 :=
  ⟨!₂[0, 1, 0], by
    norm_num [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

private def negativeAxis1 : sphere (0 : ℝ³) 1 :=
  ⟨!₂[0, -1, 0], by
    norm_num [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

private def positiveAxis2 : sphere (0 : ℝ³) 1 :=
  ⟨!₂[0, 0, 1], by
    norm_num [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

private def negativeAxis2 : sphere (0 : ℝ³) 1 :=
  ⟨!₂[0, 0, -1], by
    norm_num [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

example :
    sphereNormal (fun q ↦ (q : ℝ³)) positiveAxis0 =
      !₂[1, 0, 0] := by
  simp [positiveAxis0]

example :
    sphereNormal (fun q ↦ (q : ℝ³)) negativeAxis0 =
      !₂[-1, 0, 0] := by
  simp [negativeAxis0]

example :
    sphereNormal (fun q ↦ (q : ℝ³)) positiveAxis1 =
      !₂[0, 1, 0] := by
  simp [positiveAxis1]

example :
    sphereNormal (fun q ↦ (q : ℝ³)) negativeAxis1 =
      !₂[0, -1, 0] := by
  simp [negativeAxis1]

example :
    sphereNormal (fun q ↦ (q : ℝ³)) positiveAxis2 =
      !₂[0, 0, 1] := by
  simp [positiveAxis2]

example :
    sphereNormal (fun q ↦ (q : ℝ³)) negativeAxis2 =
      !₂[0, 0, -1] := by
  simp [negativeAxis2]

end SphereImmersionTest
