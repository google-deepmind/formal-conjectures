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
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A conjecture by Margulis on matrix groups

*Reference:* [arxiv/2504.17644](https://arxiv.org/pdf/2504.17644v3)
**Bounded diagonal orbits in homogeneous spaces over function fields**
by *Qianlin Huang, Ronggang Shi*
-/

section MatrixGroupConjecture

open Matrix SpecialLinearGroup
open scoped MatrixGroups Polynomial

section

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

-- This instance can be made more general (this is being done in
-- https://github.com/leanprover-community/mathlib4/pull/27596)
instance : TopologicalSpace (SpecialLinearGroup n ℝ) :=
  inferInstanceAs (TopologicalSpace { A : Matrix n n ℝ // A.det = 1 })

end

/- Let D be the diagonal group of SL_n(R) where n ≥ 3.
Then any relatively compact D-orbit in SL_n(R)/ SLn(Z) is closed. -/

@[category research open, AMS 11 15 22]
theorem conjecture_1_1 {n : ℕ} (hn : 3 ≤ n)
    (g : SL(n, ℝ) ⧸ Subgroup.map (map (Int.castRingHom ℝ)) ⊤)
    (hg : IsCompact <| closure (MulAction.orbit (diagonalSubgroup (Fin n) ℝ) g)) :
    IsClosed <| MulAction.orbit (diagonalSubgroup (Fin n) ℝ) g :=
  sorry

 /-!
## Diagonal orbits over function fields (Huang–Shi, Theorem 1.2)

We now formulate a Lean version of the main theorem of Huang–Shi.
Let `F` be a finite field of characteristic `p ∈ {3, 5, 7, 11}`. Set

* `A = F[t]`,
* `K = F((t⁻¹))`.

Denote by `D` the diagonal subgroup of `SL₄(K)` and by `Γ` the lattice
subgroup `SL₄(A)` embedded into `SL₄(K)` via the natural map `A →+* K`.

Then there exists a point `z : SL₄(K)/Γ` such that the `D`-orbit of `z` has
compact closure but is not closed.
-/

universe u

section FunctionFieldDiagonalOrbit

noncomputable section

variable (K : Type*) [Field K]

/-- Natural inclusion `F⟦X⟧ → F⸨X⁻¹⸩` (power series → Laurent series). -/
noncomputable def powerSeriesToLaurent : PowerSeries K→+* LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K

#check powerSeriesToLaurent


/-- Natural inclusion `Polynomial K → LaurentSeries K`
    (polynomial → power series → Laurent series). -/
def polyToLaurent : Polynomial K →+* LaurentSeries K :=
  (powerSeriesToLaurent K).comp  Polynomial.coeToPowerSeries.ringHom

#check polyToLaurent K

end
variable (F : Type u) [Field F] [Fintype F]

/-- A = F[t]. -/
abbrev A := Polynomial F

/-- K = F⸨t⁻¹⸩, the  F. -/
abbrev K := LaurentSeries F

/- Die natürliche Einbettung `F[t] →+* F((t⁻¹))`:
    Polynom → Potenzreihe → Laurentreihe. -/

noncomputable def polyToLaurent_F :
   A F →+* K F :=
  polyToLaurent (K := F)


abbrev SL4 (R : Type*) [CommRing R] :=
  Matrix.SpecialLinearGroup (Fin 4) R

/-- Group hom `SL₄(F[t]) → SL₄(F((t⁻¹)))` induced by `polyToLaurent`. -/
noncomputable def SL4_map_polyToLaurent :
    SL4 (A F) →* SL4 (K F) :=
  Matrix.SpecialLinearGroup.map (polyToLaurent F)

/-- Γ = image of `SL₄(F[t])` inside `SL₄(F((t⁻¹)))`. -/
noncomputable def Gamma : Subgroup (SL4 (K F)) :=
  (SL4_map_polyToLaurent (F := F)).range

#check diagonalSubgroup (Fin 4) (K F)


#check (inferInstance : TopologicalSpace (K F))   -- valuation topology on K

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

instance : TopologicalSpace (SpecialLinearGroup n (K F)) :=
  inferInstanceAs (TopologicalSpace { A : Matrix n n (K F) // A.det = 1 })

/-- **Huang–Shi, Theorem 1.2 (Lean statement).**

Let `F` be a finite field of characteristic `p ∈ {3, 5, 7, 11}`, and set
`K = F((t⁻¹))`, `A = F[t]`. Let

* `D` be the diagonal subgroup of `SL₄(K)`,
* `Γ = SL₄(A)` the lattice subgroup embedded into `SL₄(K)` via `polyToLaurent`.

Then there exists `z : SL₄(K)/Γ` such that the `D`-orbit of `z` has compact
closure but is not closed.
-/
@[category research open, AMS 11 15 22]
theorem huang_shi_theorem_1_2
    (hchar : ringChar (K F) ∈ ({3, 5, 7, 11} : Finset ℕ)) :
    ∃ z : SL(4, K F) ⧸ Gamma (F),
      IsCompact (closure (MulAction.orbit (diagonalSubgroup (Fin 4) (K F)) z)) ∧
      ¬ IsClosed (MulAction.orbit (diagonalSubgroup (Fin 4) (K F)) z) :=
by
  -- Placeholder: a Lean formalization would require a full development
  -- of the Huang–Shi paper in mathlib.
  sorry

end FunctionFieldDiagonalOrbit


end MatrixGroupConjecture
