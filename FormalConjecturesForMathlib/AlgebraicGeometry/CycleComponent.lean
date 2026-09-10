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

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension

/-!
# Reduced cycle components

This file constructs the reduced closed subscheme supported on the closure of a scheme point.
It proves that this subscheme is integral, identifies its specialization order with the interval
below the original point, and computes its Krull dimension as the height of that point.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

/-- The reduced closed subscheme whose underlying space is the closure of `x`. -/
def cycleComponent (X : Scheme) (x : X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subscheme

/-- The canonical closed immersion of the reduced closure of `x`. -/
def cycleComponentι (X : Scheme) (x : X) : cycleComponent X x ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι

instance (X : Scheme) (x : X) : IsClosedImmersion (cycleComponentι X x) := by
  change IsClosedImmersion
    ((Scheme.IdealSheafData.vanishingIdeal
      (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι)
  infer_instance

instance (X : Scheme) (x : X) : IsReduced (cycleComponent X x) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {x}, isClosed_closure⟩
  change IsReduced I.subscheme
  rw [IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover]
  intro U
  let U' : X.affineOpens := U
  change IsReduced (Spec (CommRingCat.of (Γ(X, U') ⧸ I.ideal U')))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  change (PrimeSpectrum.vanishingIdeal (U'.2.fromSpec ⁻¹' closure {x})).IsRadical
  exact PrimeSpectrum.isRadical_vanishingIdeal _

instance (X : Scheme) (x : X) : IrreducibleSpace (cycleComponent X x) :=
  Subtype.irreducibleSpace isIrreducible_singleton.closure

instance (X : Scheme) (x : X) : IsIntegral (cycleComponent X x) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

@[simp]
lemma range_cycleComponentι (X : Scheme) (x : X) :
    Set.range (cycleComponentι X x) = closure {x} := by
  change Set.range
    ((Scheme.IdealSheafData.vanishingIdeal
      (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι) = closure {x}
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- Membership in a reduced cycle component is membership in the closure that defines it. -/
lemma mem_cycleComponent_support_iff (X : Scheme) (x y : X) :
    y ∈ (Scheme.IdealSheafData.vanishingIdeal
        (X := X) ⟨closure {x}, isClosed_closure⟩).support ↔
      y ∈ closure {x} :=
  Set.ext_iff.mp
    (Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨closure {x}, isClosed_closure⟩) y

/-- The ambient point, regarded as a point of its reduced closure. -/
def cycleComponentGenericPoint (X : Scheme) (x : X) : cycleComponent X x :=
  ⟨x, (mem_cycleComponent_support_iff X x x).mpr (subset_closure (Set.mem_singleton x))⟩

@[simp]
lemma cycleComponentι_genericPoint (X : Scheme) (x : X) :
    cycleComponentι X x (cycleComponentGenericPoint X x) = x :=
  rfl

/-- The points of the reduced closure of `x` are exactly the specializations below `x`.

This is an order isomorphism for the specialization preorders. It is the order-theoretic core of
the dimension calculation for a cycle component. -/
def cycleComponentOrderIsoIic (X : Scheme) (x : X) :
    cycleComponent X x ≃o Set.Iic x := by
  let e : cycleComponent X x ≃ Set.Iic x :=
    { toFun := fun y ↦ ⟨cycleComponentι X x y, show cycleComponentι X x y ≤ x by
        rw [Scheme.le_iff_specializes, specializes_iff_mem_closure]
        exact (mem_cycleComponent_support_iff X x (cycleComponentι X x y)).mp y.2⟩
      invFun := fun y ↦ ⟨y.1, by
        apply (mem_cycleComponent_support_iff X x y.1).mpr
        rw [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
        exact y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine ⟨e, ?_⟩
  intro a b
  change (cycleComponentι X x a ≤ cycleComponentι X x b) ↔ a ≤ b
  rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact (cycleComponentι X x).isClosedEmbedding.isInducing.specializes_iff

@[simp]
lemma cycleComponentOrderIsoIic_apply (X : Scheme) (x : X) (y : cycleComponent X x) :
    (cycleComponentOrderIsoIic X x y : X) = cycleComponentι X x y :=
  rfl

@[simp]
lemma cycleComponentOrderIsoIic_symm_apply_coe
    (X : Scheme) (x : X) (y : Set.Iic x) :
    cycleComponentι X x ((cycleComponentOrderIsoIic X x).symm y) = y :=
  rfl

/-- The distinguished point of the reduced component corresponds to the top of the ambient
specialization interval. -/
lemma cycleComponentOrderIsoIic_genericPoint (X : Scheme) (x : X) :
    cycleComponentOrderIsoIic X x (cycleComponentGenericPoint X x) =
      ⟨x, show x ≤ x from le_rfl⟩ :=
  rfl

/-- The distinguished point is a generic point of the reduced component. -/
lemma cycleComponentGenericPoint_isGeneric (X : Scheme) (x : X) :
    IsGenericPoint (cycleComponentGenericPoint X x) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.mem_univ, iff_true]
  rw [← Scheme.le_iff_specializes, ← (cycleComponentOrderIsoIic X x).le_iff_le,
    cycleComponentOrderIsoIic_genericPoint]
  exact (cycleComponentOrderIsoIic X x y).2

/-- The explicitly constructed point agrees with the canonical generic point supplied by
integrality. -/
lemma cycleComponentGenericPoint_eq_genericPoint (X : Scheme) (x : X) :
    cycleComponentGenericPoint X x = genericPoint (cycleComponent X x) :=
  (cycleComponentGenericPoint_isGeneric X x).eq
    (genericPoint_spec (cycleComponent X x))

/-- The distinguished generic point is the top element of the component's specialization
preorder. -/
@[simp]
lemma cycleComponentGenericPoint_eq_top (X : Scheme) (x : X) :
    cycleComponentGenericPoint X x = ⊤ :=
  cycleComponentGenericPoint_eq_genericPoint X x

/-- The distinguished generic point is maximal in the component's specialization preorder. -/
lemma cycleComponentGenericPoint_isMax (X : Scheme) (x : X) :
    IsMax (cycleComponentGenericPoint X x) := by
  rw [cycleComponentGenericPoint_eq_top]
  exact isMax_top

/-- For a scheme, topological Krull dimension is the Krull dimension of its specialization
preorder. -/
lemma Scheme.topologicalKrullDim_eq_orderKrullDim (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso
    (irreducibleSetEquivPoints (α := X))

/-- The order-theoretic Krull dimension of the reduced closure of `x` is exactly the height of
`x` in the ambient scheme. -/
lemma orderKrullDim_cycleComponent (X : Scheme) (x : X) :
    Order.krullDim (cycleComponent X x) = Order.height x := by
  rw [Order.krullDim_eq_of_orderIso (cycleComponentOrderIsoIic X x)]
  exact (Order.height_eq_krullDim_Iic x).symm

/-- The topological Krull dimension of the reduced closure of `x` is exactly the order-theoretic
height of `x` in the ambient scheme. -/
lemma topologicalKrullDim_cycleComponent (X : Scheme) (x : X) :
    topologicalKrullDim (cycleComponent X x) = Order.height x := by
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim]
  exact orderKrullDim_cycleComponent X x

/-- The height of the distinguished generic point inside the component equals the ambient height
of the point defining the component. -/
lemma height_cycleComponentGenericPoint (X : Scheme) (x : X) :
    Order.height (cycleComponentGenericPoint X x) = Order.height x := by
  rw [cycleComponentGenericPoint_eq_top]
  apply WithBot.coe_eq_coe.mp
  rw [Order.height_top_eq_krullDim]
  exact orderKrullDim_cycleComponent X x

/-- The coheight of the distinguished generic point inside its component is zero. -/
@[simp]
lemma coheight_cycleComponentGenericPoint (X : Scheme) (x : X) :
    Order.coheight (cycleComponentGenericPoint X x) = 0 := by
  rw [cycleComponentGenericPoint_eq_top]
  exact Order.coheight_top _

/-- A codimension hypothesis records the ambient coheight of the generic point of the reduced
component, without changing or supplementing that hypothesis. -/
lemma cycleComponentGenericPoint_ambient_coheight
    (X : Scheme) (x : X) {p : ℕ} (hx : Order.coheight x = p) :
    Order.coheight (cycleComponentι X x (cycleComponentGenericPoint X x)) = p := by
  simpa only [cycleComponentι_genericPoint] using hx

end AlgebraicGeometry
