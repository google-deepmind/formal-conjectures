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

import FormalConjectures.Util.ProblemImports
import Mathlib/LinearAlgebra/Basis
import Mathlib/LinearAlgebra/Finsupp

noncomputable section

namespace FormalConjectures
namespace ErdosBasis

variables {K V ι : Type*} [Field K] [AddCommMonoid V] [Module K V]

/-- Build a basis from a linearly independent family `v : ι → V` that spans `⊤`. -/
def basisFromFamily (v : ι → V)
    (hLI   : LinearIndependent K v)
    (hSpan : span K (Set.range v) = ⊤) :
  Basis ι K V :=
Basis.mk hLI hSpan

/-- Coordinates of `x` in basis `b`. -/
abbrev coords (b : Basis ι K V) (x : V) : (ι →₀ K) := b.repr x

/-- Round-trip: reconstruct a vector from its coordinates. -/
@[simp] lemma total_repr (b : Basis ι K V) (x : V) : b.total (b.repr x) = x :=
b.total_repr x

/-- Round-trip: coordinates of a reconstructed vector. -/
@[simp] lemma repr_total (b : Basis ι K V) (c : ι →₀ K) : b.repr (b.total c) = c :=
b.repr_total c

end ErdosBasis
end FormalConjectures
