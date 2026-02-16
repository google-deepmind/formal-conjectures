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

/-- Let `D` be the diagonal group of `SL_n(ℝ)` where n ≥ 3.
Then any relatively compact `D`-orbit in `SL_n(ℝ) / SL_n(ℤ)` is closed. -/

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

variable (F : Type u) [Field F] [Fintype F]

/-- A = F[t]. -/
abbrev A := Polynomial F

/-- `K = F⸨t⁻¹⸩`, the field of formal Laurent series over `F`. -/
abbrev K := LaurentSeries F

abbrev SL4 (R : Type*) [CommRing R] :=
  Matrix.SpecialLinearGroup (Fin 4) R

/-- Group hom `SL₄(F[t]) → SL₄(F((t⁻¹)))` induced by the natural inclusion `F[t] →+* F((t⁻¹))`. -/
noncomputable def SL4_map_polyToLaurent :
    SL4 (A F) →* SL4 (K F) :=
  Matrix.SpecialLinearGroup.map
    ((HahnSeries.ofPowerSeries ℤ F).comp Polynomial.coeToPowerSeries.ringHom)

/-- Γ = image of `SL₄(F[t])` inside `SL₄(F((t⁻¹)))`. -/
noncomputable def Gamma : Subgroup (SL4 (K F)) :=
  (SL4_map_polyToLaurent (F := F)).range

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

instance : TopologicalSpace (SpecialLinearGroup n (K F)) :=
  inferInstanceAs (TopologicalSpace { A : Matrix n n (K F) // A.det = 1 })

/-- **Huang–Shi, Theorem 1.2 (Lean statement).**

Let `F` be a finite field of characteristic `p ∈ {3, 5, 7, 11}`, and set
`K = F((t⁻¹))`, `A = F[t]`. Let

* `D` be the diagonal subgroup of `SL₄(K)`,
* `Γ = SL₄(A)` the lattice subgroup embedded into `SL₄(K)` via the natural inclusion `A →+* K`.

Then there exists `z : SL₄(K)/Γ` such that the `D`-orbit of `z` has compact
closure but is not closed.
-/
@[category research open, AMS 11 15 22]
theorem huang_shi_theorem_1_2
    (hchar : ringChar (K F) ∈ ({3, 5, 7, 11} : Finset ℕ)) :
    ∃ z : SL(4, K F) ⧸ Gamma (F),
      IsCompact (closure (MulAction.orbit (diagonalSubgroup (Fin 4) (K F)) z)) ∧
      ¬ IsClosed (MulAction.orbit (diagonalSubgroup (Fin 4) (K F)) z) := by
  -- Placeholder: a Lean formalization would require a full development
  -- of the Huang–Shi paper in mathlib.
  sorry

end FunctionFieldDiagonalOrbit


end MatrixGroupConjecture
