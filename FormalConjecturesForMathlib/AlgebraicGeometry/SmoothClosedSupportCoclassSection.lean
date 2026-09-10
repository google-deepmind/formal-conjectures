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

public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothClosedSupportCoclassOverlap
public import FormalConjecturesForMathlib.AlgebraicTopology.SupportRelativeCohomologySheaf

/-!
# The actual global exactly normalized smooth-support coclass section

The actual holomorphic normal charts supply local relative coclasses. Their
proved ambient overlap agreement identifies their sheaf germs. Off the closed
image the actual relative complexes vanish, so those same chart germs are zero.
Unique sheaf gluing therefore constructs the global section, retaining its exact
complex normalization. No local representability or overlap coherence is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open TopCat.Presheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- The actual source open of a constructed holomorphic normal chart. -/
def smoothClosedSupportChartOpen (z : ComplexPoint Y) :
    Opens (ComplexPoint X) :=
  ⟨(closedImmersionHolomorphicFlatteningChart X Y i m d z).source,
    (closedImmersionHolomorphicFlatteningChart X Y i m d z).open_source⟩

theorem mem_smoothClosedSupportChartOpen (z : ComplexPoint Y) :
    Point.map i z ∈ smoothClosedSupportChartOpen X Y i m d z :=
  closedImmersionHolomorphicFlatteningChart_mem_source X Y i m d z

/-- The target is the sheafification of the literal relative-cohomology presheaf. -/
abbrev smoothClosedSupportCoclassSheaf : TopCat.Sheaf AddCommGrpCat
    (TopCat.of (ComplexPoint X)) :=
  supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * (d - m))

/-- The exact normal coclass determines an actual section on its full chart source. -/
def smoothClosedSupportChartSheafSection (z : ComplexPoint Y) :
    (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj
      (op (smoothClosedSupportChartOpen X Y i m d z)) :=
  (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * (d - m))).app _
      (smoothClosedSupportChartCoclass X Y i m d z
        (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))

/-- Its germ is, by definition, the germ of the fixed normal-projection coclass. -/
def smoothClosedSupportChartCoclassGerm (z : ComplexPoint Y)
    (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.stalk x :=
  supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
    (Set.range (Point.map i)) (2 * (d - m))
    (smoothClosedSupportChartOpen X Y i m d z) x hx
    (smoothClosedSupportChartCoclass X Y i m d z
      (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual ambient overlap theorem proves equality of chart germs on support. -/
theorem smoothClosedSupportChartCoclassGerm_eq
    (z z' : ComplexPoint Y) (x : ComplexPoint X)
    (hxS : x ∈ Set.range (Point.map i))
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z)
    (hx' : x ∈ smoothClosedSupportChartOpen X Y i m d z') :
    smoothClosedSupportChartCoclassGerm X Y i m d z x hx =
      smoothClosedSupportChartCoclassGerm X Y i m d z' x hx' := by
  obtain ⟨W, hW, hW', hxW, heq⟩ := exists_open_smoothClosedSupportChartCoclass_eq
    X Y i m d z z' x hxS hx hx'
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
    (U := smoothClosedSupportChartOpen X Y i m d z)
    (V := smoothClosedSupportChartOpen X Y i m d z')
    hW hW' x hxW
  simpa only [smoothClosedSupportChartCoclass_restrict] using heq

/-- Away from the actual closed image, the actual chart coclass germ is zero. -/
theorem smoothClosedSupportChartCoclassGerm_eq_zero
    (z : ComplexPoint Y) (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z)
    (hxS : x ∉ Set.range (Point.map i)) :
    smoothClosedSupportChartCoclassGerm X Y i m d z x hx = 0 :=
  supportRelativeCohomologyGerm_eq_zero_of_not_mem
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
    (isClosed_range_map_of_closedImmersion i)
    (smoothClosedSupportChartOpen X Y i m d z) x hx hxS
    (smoothClosedSupportChartCoclass X Y i m d z
      (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))

/-- A pointwise normalized germ family. Choice selects a preimage point only;
the proved chart-overlap theorem below proves independence of that selection. -/
def smoothClosedSupportCoclassStalk (x : ComplexPoint X) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.stalk x := by
  classical
  exact if hxS : x ∈ Set.range (Point.map i) then
    smoothClosedSupportChartCoclassGerm X Y i m d hxS.choose x
      (by simpa only [hxS.choose_spec] using
        mem_smoothClosedSupportChartOpen X Y i m d hxS.choose)
  else 0

/-- The normalized germ family agrees with every actual chart, including at points
outside the support. This supplies local coherence as a theorem, not as data. -/
theorem smoothClosedSupportCoclassStalk_eq_chartGerm
    (z : ComplexPoint Y) (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z) :
    smoothClosedSupportCoclassStalk X Y i m d x =
      smoothClosedSupportChartCoclassGerm X Y i m d z x hx := by
  by_cases hxS : x ∈ Set.range (Point.map i)
  · rw [smoothClosedSupportCoclassStalk, dif_pos hxS]
    exact smoothClosedSupportChartCoclassGerm_eq X Y i m d
      hxS.choose z x hxS _ hx
  · rw [smoothClosedSupportCoclassStalk, dif_neg hxS]
    exact (smoothClosedSupportChartCoclassGerm_eq_zero X Y i m d z x hx hxS).symm

@[simp] theorem smoothClosedSupportCoclassStalk_eq_zero
    (x : ComplexPoint X) (hxS : x ∉ Set.range (Point.map i)) :
    smoothClosedSupportCoclassStalk X Y i m d x = 0 := by
  rw [smoothClosedSupportCoclassStalk, dif_neg hxS]

/-- Actual charts and the open support complement prove local representability
of the entire normalized stalk family. -/
theorem smoothClosedSupportCoclassStalk_locallyRepresentable :
    ∀ x : ComplexPoint X,
      ∃ (U : Opens (ComplexPoint X)) (_ : x ∈ U)
        (s : (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj (op U)),
        ∀ (y : ComplexPoint X) (hy : y ∈ U),
          (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.germ U y hy s =
            smoothClosedSupportCoclassStalk X Y i m d y := by
  intro x
  by_cases hxS : x ∈ Set.range (Point.map i)
  · obtain ⟨z, rfl⟩ := hxS
    refine ⟨smoothClosedSupportChartOpen X Y i m d z,
      mem_smoothClosedSupportChartOpen X Y i m d z,
      smoothClosedSupportChartSheafSection X Y i m d z, ?_⟩
    exact fun y hy ↦ (smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z y hy).symm
  · let U : Opens (ComplexPoint X) :=
      ⟨(Set.range (Point.map i))ᶜ, (isClosed_range_map_of_closedImmersion i).isOpen_compl⟩
    refine ⟨U, hxS, 0, ?_⟩
    intro y hy
    rw [map_zero, smoothClosedSupportCoclassStalk_eq_zero X Y i m d y hy]

/-- The actual unique global gluing of exactly normalized smooth normal coclasses. -/
def smoothClosedSupportCoclassSection :
    (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj (op ⊤) :=
  TopCat.Sheaf.sectionOfLocallyRepresentable _
    (smoothClosedSupportCoclassStalk X Y i m d)
    (smoothClosedSupportCoclassStalk_locallyRepresentable X Y i m d)

@[simp] theorem smoothClosedSupportCoclassSection_germ (x : ComplexPoint X) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection X Y i m d) =
        smoothClosedSupportCoclassStalk X Y i m d x :=
  TopCat.Sheaf.sectionOfLocallyRepresentable_germ
    (smoothClosedSupportCoclassSheaf X Y i m d)
    (smoothClosedSupportCoclassStalk X Y i m d)
    (smoothClosedSupportCoclassStalk_locallyRepresentable X Y i m d) x

/-- Exact stalk normalization in every actual normal chart. -/
theorem smoothClosedSupportCoclassSection_germ_eq_chart
    (z : ComplexPoint Y) (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen X Y i m d z) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection X Y i m d) =
        smoothClosedSupportChartCoclassGerm X Y i m d z x hx := by
  rw [smoothClosedSupportCoclassSection_germ,
    smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z x hx]

/-- The global section restricts to the actual normalized section on a full normal chart. -/
theorem smoothClosedSupportCoclassSection_restrict_chart (z : ComplexPoint Y) :
    (smoothClosedSupportCoclassSheaf X Y i m d).obj.map
      (homOfLE (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top)).op
      (smoothClosedSupportCoclassSection X Y i m d) =
        smoothClosedSupportChartSheafSection X Y i m d z := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf X Y i m d)
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact smoothClosedSupportCoclassSection_germ_eq_chart X Y i m d z x hx

/-- Outside the actual image, the global section has zero germ. -/
theorem smoothClosedSupportCoclassSection_germ_eq_zero
    (x : ComplexPoint X) (hxS : x ∉ Set.range (Point.map i)) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection X Y i m d) = 0 := by
  rw [smoothClosedSupportCoclassSection_germ,
    smoothClosedSupportCoclassStalk_eq_zero X Y i m d x hxS]

/-- Uniqueness of the actual gluing, expressed by its exact stalk normalization. -/
theorem smoothClosedSupportCoclassSection_unique
    (s : (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj (op ⊤))
    (hs : ∀ x : ComplexPoint X,
      (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x s =
        smoothClosedSupportCoclassStalk X Y i m d x) :
    s = smoothClosedSupportCoclassSection X Y i m d := by
  apply TopCat.Presheaf.section_ext (smoothClosedSupportCoclassSheaf X Y i m d)
  exact fun x _ ↦ (hs x).trans (smoothClosedSupportCoclassSection_germ X Y i m d x).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- At every center, the global section has exactly the germ of the previously
constructed normal-slice coclass, on any prescribed local model neighborhood. -/
theorem smoothClosedSupportCoclassSection_germ_eq_normalCoclass
    (z : ComplexPoint Y) (V : Opens (ComplexPoint X))
    (hzV : Point.map i z ∈ V) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm
      (Point.map i z) (smoothClosedSupportCoclassSection X Y i m d) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m))
      (smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (Point.map i z) (mem_smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (smoothClosedSupportNormalCoclass X Y i m d z V hzV) := by
  let C := smoothClosedSupportChartOpen X Y i m d z
  let U := smoothClosedSupportNeighborhood X Y i m d z V hzV
  let W := C ⊓ U
  have hWC : W ≤ C := inf_le_left
  have hWU : W ≤ U := inf_le_right
  have hzW : Point.map i z ∈ W :=
    ⟨mem_smoothClosedSupportChartOpen X Y i m d z,
      mem_smoothClosedSupportNeighborhood X Y i m d z V hzV⟩
  rw [smoothClosedSupportCoclassSection_germ_eq_chart X Y i m d z
    (Point.map i z) (mem_smoothClosedSupportChartOpen X Y i m d z)]
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
    hWC hWU (Point.map i z) hzW
  rw [smoothClosedSupportChartCoclass_restrict,
    smoothClosedSupportNormalCoclass_restrict_eq_chart X Y i m d z V hzV W hWU hWC]

/-- The fixed chart normalization at support centers and zero germs off support
uniquely characterize the global section, independently of preimage choices. -/
theorem smoothClosedSupportCoclassSection_unique_of_normalization
    (s : (smoothClosedSupportCoclassSheaf X Y i m d).obj.obj (op ⊤))
    (hs : ∀ z : ComplexPoint Y,
      (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm (Point.map i z) s =
        smoothClosedSupportChartCoclassGerm X Y i m d z (Point.map i z)
          (mem_smoothClosedSupportChartOpen X Y i m d z))
    (hzero : ∀ (x : ComplexPoint X), x ∉ Set.range (Point.map i) →
      (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x s = 0) :
    s = smoothClosedSupportCoclassSection X Y i m d := by
  apply smoothClosedSupportCoclassSection_unique
  intro x
  by_cases hxS : x ∈ Set.range (Point.map i)
  · obtain ⟨z, rfl⟩ := hxS
    exact (hs z).trans (smoothClosedSupportCoclassStalk_eq_chartGerm
      X Y i m d z (Point.map i z)
      (mem_smoothClosedSupportChartOpen X Y i m d z)).symm
  · rw [hzero x hxS, smoothClosedSupportCoclassStalk_eq_zero X Y i m d x hxS]

end AlgebraicGeometry.ComplexPoint
