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

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Topology.LocallyFinsupp

/-!
# Finiteness of principal divisors

The order-of-vanishing function of a nonzero rational function on an integral Noetherian scheme
has finite support. Indeed, the function is a unit on a nonempty open set. Every codimension-one
point in its complement is the generic point of one of the complement's finitely many irreducible
components. This supplies the local-finiteness proof needed to regard the divisor as an algebraic
cycle.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A nonzero rational function on an integral Noetherian scheme has only finitely many
codimension-one zeros and poles. -/
theorem Scheme.ord_support_finite [IsIntegral X] [IsNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) :
    (Function.support (X.ord f)).Finite := by
  obtain ⟨U, _, f', hUne, hgf, hfunit⟩ := exists_isUnit_germ_eq X f hf
  let Z : Set X := Uᶜ
  obtain ⟨S, hSfinite, hSclosed, hSirred, hZ⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible
      (show IsClosed Z from U.isOpen.isClosed_compl)
  let : Finite S := hSfinite
  let : PartialOrder X := specializationOrder X
  let g : S → X := fun T ↦ (hSirred T.1 T.2).genericPoint
  apply (Set.finite_range g).subset
  intro x hx
  have hxord : X.ord f x ≠ 0 := Function.mem_support.mp hx
  have hxcodim : coheight x = 1 := by
    by_contra h
    exact hxord (X.ord_eq_zero_of_coheight_neq_one h f)
  have hxnotU : x ∉ U := by
    intro hxU
    apply hxord
    rw [← hgf]
    exact X.ord_of_isUnit hfunit hxU
  have hxZ : x ∈ Z := hxnotU
  rw [hZ] at hxZ
  obtain ⟨T, hTS, hxT⟩ := Set.mem_sUnion.mp hxZ
  let T' : S := ⟨T, hTS⟩
  refine ⟨T', ?_⟩
  let y : X := g T'
  have hyclosure : closure ({y} : Set X) = T :=
    (hSirred T hTS).closure_genericPoint (hSclosed T hTS)
  have hyx : y ⤳ x := by
    rw [specializes_iff_mem_closure, hyclosure]
    exact hxT
  have hxy : x ≤ y := hyx
  change y = x
  apply le_antisymm
  · by_contra hnyx
    have hxy_ne : x ≠ y := fun h ↦ hnyx (h ▸ le_rfl)
    have hxylt : x < y := lt_of_le_of_ne hxy hxy_ne
    have hycodim_le : coheight y ≤ 0 :=
      ((Order.coheight_eq_coe_add_one_iff (x := x) (n := 0)).mp hxcodim).2.2 y hxylt
    have hycodim : coheight y = 0 := bot_unique hycodim_le
    have hymax : IsMax y := Order.coheight_eq_zero.mp hycodim
    have hytop : y = (⊤ : X) := hymax.eq_of_le (le_top : y ≤ (⊤ : X))
    have hTuniv : T = Set.univ := by
      rw [← hyclosure, hytop]
      exact genericPoint_closure X
    have hTZ : T ⊆ Z := by
      intro z hz
      rw [hZ]
      exact Set.mem_sUnion_of_mem hz hTS
    obtain ⟨z, hzU⟩ := hUne
    have hzT : z ∈ T := by rw [hTuniv]; trivial
    exact hTZ hzT hzU
  · exact hxy

/-- The order-of-vanishing function is locally finitely supported, hence defines an algebraic
cycle without an additional finiteness hypothesis. -/
theorem Scheme.ord_locallyFiniteSupport [IsIntegral X] [IsNoetherian X]
    (f : X.functionField) : LocallyFiniteSupport (X.ord f) := by
  by_cases hf : f = 0
  · exact fun _ ↦ ⟨Set.univ, Filter.univ_mem, by simp [hf]⟩
  exact fun _ ↦ ⟨Set.univ, Filter.univ_mem, by simpa using X.ord_support_finite f hf⟩

end AlgebraicGeometry
