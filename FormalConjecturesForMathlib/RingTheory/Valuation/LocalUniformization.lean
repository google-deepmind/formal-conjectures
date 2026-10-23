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

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Centres of valuation subrings and local uniformization

Let `F` be a field over a field `k` and let `𝒪` be a valuation subring of `F`. For a
`k`-subalgebra `A` of `F` contained in `𝒪`, the *centre* of `𝒪` on `A` is the prime ideal
`𝔪_𝒪 ∩ A` of `A`: the point of the affine model `Spec A` whose local ring `𝒪` dominates.

`𝒪` *admits local uniformization over* `k` if some finitely generated `k`-subalgebra `A ⊆ 𝒪` with
fraction field `F` is regular at the centre of `𝒪`. Following Knaf and Kuhlmann, the condition is
that the centre is a regular point, not a smooth one, which is the right notion over an imperfect
ground field.

## Main definitions

* `ValuationSubring.centerOn`: the centre of a valuation subring on a subalgebra it contains.
* `ValuationSubring.HasLocalUniformization`: some affine model is regular at the centre.

## References

- H. Knaf and F.-V. Kuhlmann, [Every place admits local uniformization in a finite extension of
  the function field](https://doi.org/10.1016/j.aim.2008.12.009), Adv. Math. 221 (2009), 428--453.
-/

@[expose] public section

open IsLocalRing

namespace ValuationSubring

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra k F]

/--
The *centre* of a valuation subring `𝒪` of `F` on a `k`-subalgebra `A` of `F` contained in `𝒪`:
the prime ideal `𝔪_𝒪 ∩ A` of `A`.
-/
def centerOn (𝒪 : ValuationSubring F) (A : Subalgebra k F) (hA : ∀ a : A, (a : F) ∈ 𝒪) :
    Ideal A :=
  (maximalIdeal 𝒪).comap (A.val.toRingHom.codRestrict 𝒪 hA)

/-- The centre of `𝒪` on `A` is a prime ideal of `A`. -/
instance (𝒪 : ValuationSubring F) (A : Subalgebra k F) (hA : ∀ a : A, (a : F) ∈ 𝒪) :
    (𝒪.centerOn A hA).IsPrime :=
  Ideal.IsPrime.comap _

/-- The centre of `𝒪` on `A` consists of the elements of `A` of valuation less than one. -/
theorem mem_centerOn_iff (𝒪 : ValuationSubring F) (A : Subalgebra k F)
    (hA : ∀ a : A, (a : F) ∈ 𝒪) (a : A) :
    a ∈ 𝒪.centerOn A hA ↔ 𝒪.valuation (a : F) < 1 := by
  rw [centerOn, Ideal.mem_comap, valuation_lt_one_iff]
  rfl

/--
A valuation subring `𝒪` of `F` *admits local uniformization over* `k` if some affine model of
`F` over `k` inside `𝒪` is regular at the centre of `𝒪`: there is a finitely generated
`k`-subalgebra `A` of `F` with `A ⊆ 𝒪` and fraction field `F` whose localisation at the centre
of `𝒪` is a regular local ring.
-/
def HasLocalUniformization (𝒪 : ValuationSubring F) (k : Type*) [Field k] [Algebra k F] : Prop :=
  ∃ (A : Subalgebra k F) (hA : ∀ a : A, (a : F) ∈ 𝒪),
    Algebra.FiniteType k A ∧ IsFractionRing A F ∧
      IsRegularLocalRing (Localization.AtPrime (𝒪.centerOn A hA))

/-- A regular affine model of `F` over `k` inside `𝒪` uniformizes `𝒪`. -/
theorem hasLocalUniformization_of_isRegularRing (𝒪 : ValuationSubring F) (A : Subalgebra k F)
    (hA : ∀ a : A, (a : F) ∈ 𝒪) [Algebra.FiniteType k A] [IsFractionRing A F]
    [IsRegularRing A] : 𝒪.HasLocalUniformization k :=
  ⟨A, hA, ‹_›, ‹_›, IsRegularRing.isRegularLocalRing_localization _⟩

end ValuationSubring
