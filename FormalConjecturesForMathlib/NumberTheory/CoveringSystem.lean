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

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Ideal.Defs

open Pointwise

/--
A covering system of a semiring `R` is a finite set of cosets of non-zero ideals whose union
covers the whole ring. In the case where `R = ℤ`, this corresponds to a choice of finitely many
congruence relations such that every integer satisfies at least one of the relations.
-/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, {residue i} + (moduli i : Set R) = @Set.univ R
  non_trivial : ∀ i, moduli i ≠ ⊥

/--
We say a covering system is strict if all the congruence relations that define it are take modulo
a different ideal (or number).

Note: this corresponds to the notion of a covering system that Erdos was using in
[ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number theory. Monographies de L'Enseignement Mathematique (1980).
-/
structure StrictCoveringSystem (R : Type*) [CommSemiring R] extends CoveringSystem R where
  injective_moduli : moduli.Injective

namespace CoveringSystem

variable {R : Type*} [CommSemiring R]

def coset (c : CoveringSystem R) (i : c.ι) : Set R :=
  {c.residue i} + c.moduli i

@[simp]
theorem iUnion_cosets (c : CoveringSystem R) : ⋃ i, c.coset i = Set.univ :=
  c.unionCovers

end CoveringSystem
