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

public import FormalConjecturesUtil

/-!
# Moving Sofa Problem

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Moving_sofa_problem)
- [Ge92] Gerver, J. L., _On moving a sofa around a corner_. Geometriae Dedicata 42.3 (1992): 267-283.
- [Ro18] Romik, D. _Differential equations and exact solutions in the moving sofa problem_. Experimental mathematics 27.3 (2018): 316-330.
- [Ba24] Baek, J. _Optimality of Gerver's Sofa_. arXiv preprint arXiv:2411.19826 (2024).
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

/-- The **horizontal side** of the hallway is $(-\infty, 1] \times [0, 1]$. -/
def horizontalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The **vertical side** of the hallway is $[0, 1] \times (-\infty, 1]$. -/
def verticalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

/-- The **hallway** is the union of its horizontal and vertical sides. -/
def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

instance : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

/--
A connected closed set $s$ is a **moving sofa** according to a rigid motion $m:I\to\mathrm{SE}(2)$,
if the sofa is initially in the horizontal side of the hallway and ends up in the vertical side.
Here, since $\mathrm{SE}(2)$ is not in Mathlib yet, we use $\mathrm{E}(2)$ and rely on continuity
and $m(0) = \mathrm{id}$ to ensure $m$ is in $\mathrm{SE}(2)$.
-/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

/-- The unit square. -/
def unitSquare : Set ℝ² := parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- Coordinates of points in the unit square lie in `[0,1]`. -/
@[category API, AMS 49]
private lemma mem_Icc_of_mem_unitSquare {p : ℝ²} (hp : p ∈ unitSquare) (i : Fin 2) :
    p i ∈ Set.Icc (0:ℝ) 1 := by
  have h := parallelepiped_basis_eq (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [unitSquare, show parallelepiped ⇑(EuclideanSpace.basisFun (Fin 2) ℝ) =
    parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis by
      rw [OrthonormalBasis.coe_toBasis], h] at hp
  simpa using hp i

/--
The unit square $[0,1]^2$ is a valid moving sofa (with the identity motion).
It sits in the corner where both hallways overlap, so the stationary motion works.
This is a sanity check that the `IsMovingSofa` definition is not vacuous.
-/
@[category test, AMS 49]
theorem isMovingSofa_unitSquare : ∃ m, IsMovingSofa unitSquare m := by
  refine ⟨fun _ => .refl ℝ ℝ², ?_, ?_, continuous_const, rfl, ?_, ?_, ?_⟩
  · unfold unitSquare parallelepiped
    refine ⟨⟨0, 0, by simp, by simp⟩, (convex_Icc _ _).isPreconnected.image _ ?_⟩
    exact (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const).continuousOn
  · unfold unitSquare parallelepiped
    exact (isCompact_Icc.image
      (continuous_finsetSum _ fun i _ =>
        (continuous_apply i).smul continuous_const)).isClosed
  · intro p hp
    have h0 := mem_Icc_of_mem_unitSquare hp 0
    have h1 := mem_Icc_of_mem_unitSquare hp 1
    exact ⟨p 0, p 1, ⟨h0.2.trans (by norm_num), h1.1, h1.2⟩,
      by ext i; fin_cases i <;> rfl⟩
  · rintro t q ⟨p, hp, rfl⟩
    rw [show (AffineIsometryEquiv.refl ℝ ℝ²) p = p from rfl]
    refine .inl ?_
    have h0 := mem_Icc_of_mem_unitSquare hp 0
    have h1 := mem_Icc_of_mem_unitSquare hp 1
    exact ⟨p 0, p 1, ⟨h0.2.trans (by norm_num), h1.1, h1.2⟩,
      by ext i; fin_cases i <;> rfl⟩
  · rintro q ⟨p, hp, rfl⟩
    rw [show (AffineIsometryEquiv.refl ℝ ℝ²) p = p from rfl]
    have h0 := mem_Icc_of_mem_unitSquare hp 0
    have h1 := mem_Icc_of_mem_unitSquare hp 1
    exact ⟨p 0, p 1, ⟨h0.1, h0.2, h1.2.trans (by norm_num)⟩,
      by ext i; fin_cases i <;> rfl⟩

/--
The rigid motion that translates by $p$ and then rotates counterclockwise by $\alpha$.
Note that [Ge92] used this definition while [Ro18] used rotation first and then translation.
-/
def rotateTranslate (α : Real.Angle) (p : ℝ²) : E(2) :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans
    (EuclideanGeometry.o.rotation α).toAffineIsometryEquiv

/-- `rotateTranslate α p` sends $q$ to $R_\alpha(q + p)$: the translation is applied first. -/
@[category test, AMS 49]
theorem rotateTranslate_apply (α : Real.Angle) (p q : ℝ²) :
    rotateTranslate α p q = EuclideanGeometry.o.rotation α (q + p) := rfl

/--
The sofa according to a rotation path $p : [0, \pi/2] \to \mathbb{R}^2$ as in [Ge92] is the
intersection over $\alpha \in [0, \pi/2]$ of hallways each translated by $p(\alpha)$ and then
rotated by $\alpha$, with the special cases that the hallway at $0$ is the horizontal side
and the hallway at $\pi/2$ is the vertical side.
-/
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

namespace GerversSofa

/-
Gerver's constants defining the sofa.

This section follows Theorem 2 of Gerver's paper [Ge92].
-/

/--
Eq. 1-4 of [Ro18], which specifies the constants $A$, $B$, $\varphi$, and $\theta$ of [Ge92].
-/
def ABφθSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

/-- There exist unique constants $A$, $B$, $\varphi$, and $\theta$ satisfying the spec. -/
@[category textbook, AMS 49]
theorem ABφθSpec.existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 :=
  sorry

def A : ℝ := ABφθSpec.existsUnique.choose.1
def B : ℝ := ABφθSpec.existsUnique.choose.2.1
def φ : ℝ := ABφθSpec.existsUnique.choose.2.2.1
def θ : ℝ := ABφθSpec.existsUnique.choose.2.2.2

def r (α : ℝ) : ℝ :=
  if α ≤ φ then
    1 / 2
  else if α ≤ θ then
    (1 + A + α - φ) / 2
  else if α ≤ π / 2 - θ then
    A + α - φ
  else if α ≤ π / 2 - φ then
    B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ) ^ 2 / 4
  else
    0

def y (α : ℝ) : ℝ :=
  ∫ t in α..π / 2 - φ, r t * t.sin

def x (α : ℝ) : ℝ :=
  1 - ∫ t in α..π / 2 - φ, r t * t.cos

def p (α : ℝ) : ℝ² :=
  !₂[if α ≤ φ
      then α.cos - 1
      else x (π / 2 - α) * α.cos + y (π / 2 - α) * α.sin - 1,
    if α ≤ π / 2 - φ
      then y α * α.cos - (4 * x 0 - 2 - x α) * α.sin - 1
      else -(4 * x 0 - 3) * α.sin - 1]

end GerversSofa

/-- Gerver's sofa is the sofa according to the rotation path `GerversSofa.p`. -/
def gerversSofa : Set ℝ² :=
  sofaOfRotateTranslatePath GerversSofa.p

/-- Gerver's concrete sofa admits a valid hallway motion. -/
@[category research solved, AMS 49,
  formal_proof using lean4 at "https://github.com/dawidmtrela-dotcom/GerverSofaLean/releases/tag/v1.1.0"]
theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m := by
  sorry

open MeasureTheory
open scoped ENNReal

/-- The **sofa constant** is the maximal area of a moving sofa. -/
def sofaConstant : ℝ≥0∞ := ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

/-- The sofa constant is at least 1, as witnessed by the unit square. -/
@[category test, AMS 49]
theorem one_le_sofaConstant : 1 ≤ sofaConstant := by
  calc
    _ = volume unitSquare := (OrthonormalBasis.volume_parallelepiped _).symm
    _ ≤ sofaConstant := le_iSup₂ (α := ℝ≥0∞) unitSquare isMovingSofa_unitSquare

/-- What is the sofa constant? -/
@[category research solved, AMS 49]
theorem sofaConstant_eq : sofaConstant = answer(volume gerversSofa) := by
  sorry

/-- Gerver's sofa attains the sofa constant, conjectured by [Ge92] and claimed by [Ba24]. -/
@[category research solved, AMS 49]
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa := by
  sorry

/--
Gerver's sofa is the unique sofa that attains the sofa constant, up to a rigid motion.

The motion is needed: `horizontalHallway` is $(-\infty, 1] \times [0, 1]$, so a leftward
translate of any moving sofa is again one, obtained by sliding right and then following the
original motion. It has the same area, so uniqueness cannot hold on the nose.
-/
@[category research open, AMS 49]
theorem volume_eq_sofaConstant_iff_congruent_gerversSofa (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s = sofaConstant ↔ ∃ g : E(2), s = g '' gerversSofa := by
  sorry

/-!
## The ambidextrous sofa

Romik [Ro18, §1.2] asks for the largest shape that can turn both right and left around the
corner. Following [Ro18, Thm. 5], a shape is ambidextrous if both it and its reflection
$\rho(x, y) = (x, 1 - y)$ are moving sofas: $\rho$ fixes `horizontalHallway` and turns `hallway`
into its mirror image. The line of reflection is fixed, so both turns start from the same
placement; otherwise every moving sofa would be ambidextrous, by reflecting a motion in the
diagonal $x = y$ and reversing time.
-/

/-- The horizontal line $y = 1/2$, the axis of symmetry of the horizontal side of the hallway. -/
def midline : AffineSubspace ℝ ℝ² :=
  AffineSubspace.mk' !₂[0, 1 / 2] (ℝ ∙ (EuclideanSpace.basisFun (Fin 2) ℝ 0))

instance : Nonempty midline := ⟨⟨_, AffineSubspace.self_mem_mk' _ _⟩⟩

/-- Sanity check: reflection in `midline` acts as $(x, y) \mapsto (x, 1 - y)$. -/
@[category test, AMS 49]
theorem reflection_midline_apply (q : ℝ²) :
    EuclideanGeometry.reflection midline q = !₂[q 0, 1 - q 1] := by
  rw [EuclideanGeometry.reflection_apply_of_mem midline q (AffineSubspace.self_mem_mk' _ _),
    midline, AffineSubspace.direction_mk', Submodule.reflection_apply,
    Submodule.starProjection_singleton]
  ext i
  fin_cases i <;> simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.vecHead] <;> ring

/-- A set closed under reflection in `midline` is its own image. -/
@[category API, AMS 49]
private lemma reflection_midline_image_eq_self {S : Set ℝ²}
    (h : ∀ p ∈ S, EuclideanGeometry.reflection midline p ∈ S) :
    EuclideanGeometry.reflection midline '' S = S :=
  Set.Subset.antisymm (Set.image_subset_iff.2 h) fun p hp =>
    ⟨_, h p hp, EuclideanGeometry.reflection_reflection midline p⟩

/-- Sanity check: reflection in `midline` fixes the horizontal side of the hallway. -/
@[category test, AMS 49]
theorem reflection_midline_image_horizontalHallway :
    EuclideanGeometry.reflection midline '' horizontalHallway = horizontalHallway := by
  refine reflection_midline_image_eq_self ?_
  rintro _ ⟨x, y, ⟨hx, hy0, hy1⟩, rfl⟩
  rw [reflection_midline_apply]
  exact ⟨x, 1 - y, ⟨by simpa using hx, by simp; linarith, by simp; linarith⟩, by simp⟩

/-- A point lies in the unit square iff both coordinates lie in `[0,1]`. -/
@[category API, AMS 49]
private lemma mem_unitSquare_iff {p : ℝ²} : p ∈ unitSquare ↔ ∀ i, p i ∈ Set.Icc (0:ℝ) 1 := by
  rw [unitSquare, ← OrthonormalBasis.coe_toBasis, parallelepiped_basis_eq]
  simp

/-- Sanity check: the unit square is symmetric under reflection in `midline`. -/
@[category test, AMS 49]
theorem reflection_midline_image_unitSquare :
    EuclideanGeometry.reflection midline '' unitSquare = unitSquare := by
  refine reflection_midline_image_eq_self fun p hp => ?_
  rw [mem_unitSquare_iff] at hp ⊢
  intro i
  rw [reflection_midline_apply]
  fin_cases i
  · simpa using hp 0
  · have := hp 1
    simp only [Set.mem_Icc] at this ⊢
    constructor <;> simp <;> linarith [this.1, this.2]

/-- A closed connected set is an **ambidextrous sofa** if both it and its reflection in `midline`
are moving sofas [Ro18, Thm. 5]. -/
def IsAmbidextrousSofa (s : Set ℝ²) : Prop :=
  (∃ m, IsMovingSofa s m) ∧ (∃ m, IsMovingSofa (EuclideanGeometry.reflection midline '' s) m)

/-- Sanity check: the unit square is ambidextrous. -/
@[category test, AMS 49]
theorem isAmbidextrousSofa_unitSquare : IsAmbidextrousSofa unitSquare :=
  ⟨isMovingSofa_unitSquare,
    by rw [reflection_midline_image_unitSquare]; exact isMovingSofa_unitSquare⟩

/-- The **ambidextrous sofa constant** is the maximal area of an ambidextrous sofa. -/
def ambidextrousSofaConstant : ℝ≥0∞ :=
  ⨆ (s : Set ℝ²) (_ : IsAmbidextrousSofa s), volume s

/-- The ambidextrous sofa constant is at least 1, as witnessed by the unit square. -/
@[category test, AMS 49]
theorem one_le_ambidextrousSofaConstant : 1 ≤ ambidextrousSofaConstant := by
  calc
    _ = volume unitSquare := (OrthonormalBasis.volume_parallelepiped _).symm
    _ ≤ ambidextrousSofaConstant :=
      le_iSup₂ (α := ℝ≥0∞) unitSquare isAmbidextrousSofa_unitSquare

/-- Every ambidextrous sofa is a moving sofa. -/
@[category test, AMS 49]
theorem ambidextrousSofaConstant_le_sofaConstant :
    ambidextrousSofaConstant ≤ sofaConstant :=
  iSup₂_le fun s hs => le_iSup₂ (α := ℝ≥0∞) s hs.1

namespace RomiksSofa

/-- The cubic $x^2 (x + 3) = 8$ has exactly one real root. -/
@[category test, AMS 49]
theorem existsUnique_X : ∃! x : ℝ, x ^ 2 * (x + 3) = 8 := by
  have hc : Continuous (fun x : ℝ => x ^ 2 * (x + 3)) := by fun_prop
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (a := (0:ℝ)) (b := 2) (by norm_num)
    hc.continuousOn (show (8:ℝ) ∈ Set.Icc _ _ by norm_num)
  refine ⟨x, hx, fun y hy => ?_⟩
  have hx0 : 0 < x := by nlinarith [sq_nonneg (x + 2), sq_nonneg x]
  have hy0 : 0 < y := by nlinarith [sq_nonneg (y + 2), sq_nonneg y]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx0 hy0]

/-- The cubic $x (4 x^2 + 3) = 1$ has exactly one real root. -/
@[category test, AMS 49]
theorem existsUnique_Y : ∃! x : ℝ, x * (4 * x ^ 2 + 3) = 1 := by
  have hc : Continuous (fun x : ℝ => x * (4 * x ^ 2 + 3)) := by fun_prop
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (a := (0:ℝ)) (b := 1) (by norm_num)
    hc.continuousOn (show (1:ℝ) ∈ Set.Icc _ _ by norm_num)
  refine ⟨x, hx, fun y hy => ?_⟩
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]

/-- $X = \sqrt[3]{3 + 2\sqrt2} + \sqrt[3]{3 - 2\sqrt2} - 1 ≈ 1.3553$, the real root of
$x^2 (x + 3) = 8$. -/
def X : ℝ := existsUnique_X.exists.choose

/-- $Y = \tfrac12\bigl(\sqrt[3]{\sqrt2 + 1} - \sqrt[3]{\sqrt2 - 1}\bigr) ≈ 0.2980$, the real root of
$x (4 x^2 + 3) = 1$. -/
def Y : ℝ := existsUnique_Y.exists.choose

/--
The area of Romik's ambidextrous sofa is $X + \arctan Y ≈ 1.644955218425440$ [Ro18, eq. (5)].
The shape itself, bounded by 18 arcs of circles and sextic curves [Ro18, §5–6], is not defined here.
-/
def area : ℝ := X + Real.arctan Y

end RomiksSofa

/--
Romik's ambidextrous sofa has area `RomiksSofa.area` [Ro18, Thm. 5], so the ambidextrous sofa
constant is at least that.
-/
@[category research solved, AMS 49]
theorem romiksSofa_area_le_ambidextrousSofaConstant :
    ENNReal.ofReal RomiksSofa.area ≤ ambidextrousSofaConstant := by
  sorry

/--
Romik's ambidextrous sofa is optimal. Romik derived it from local-optimality considerations and
proposed it as the solution [Ro18, §1.2, §5]; [Wikipedia] records it as the conjectured optimum.
Even its local optimality is open [Ro18, §7, Problem 1].
-/
@[category research open, AMS 49]
theorem ambidextrousSofaConstant_eq_romiksSofa_area :
    ambidextrousSofaConstant = ENNReal.ofReal RomiksSofa.area := by
  sorry

end MovingSofa
