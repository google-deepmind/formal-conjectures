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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothClosedSupportCoclassOverlap
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SupportRelativeCohomologySheaf
/-!
# The global normalized smooth-support coclass section

Holomorphic normal charts supply local relative coclasses whose ambient overlap agreement
identifies their sheaf germs, and those germs vanish off the closed image because the
relative complexes do. Unique sheaf gluing then produces the global section, with its
complex normalization.
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
private theorem smoothClosedSupportChartCoclassGerm_eq
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
private theorem smoothClosedSupportChartCoclassGerm_eq_zero
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

end AlgebraicGeometry.ComplexPoint
