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

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

public section

namespace Affine.Simplex
variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] [PartialOrder k]
  [ZeroLEOneClass k] {n : ℕ}

@[simp] lemma closedInterior_nonempty (s : Simplex k P n) : s.closedInterior.Nonempty :=
  ⟨_, s.point_mem_closedInterior 0⟩

end Affine.Simplex
