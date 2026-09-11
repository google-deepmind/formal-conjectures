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

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# The subgroups in the Borel-Jacquet definition of an automorphic form

The subgroups of `G(𝔸) = G(𝔸_f) × G(ℝ)`, for `G = GL n / ℚ`, that the Borel-Jacquet
definition of an automorphic form quantifies over; see
`FormalConjecturesForMathlib.NumberTheory.AutomorphicForm.BorelJacquet` for that definition,
and Borel and Jacquet's Corvallis article, the reference below, for its source.

## Main declarations

All in the namespace `Matrix.GeneralLinearGroup`:

* `diagonalEmbedding` and `ratDiagonal`: the diagonal copy of the rational points
  `Γ = G(ℚ) = GL n ℚ` in `G(𝔸_f) × G(ℝ)`, the subgroup of condition (a).
* `orthogonalSubgroup`: the orthogonal group `K = O n ℝ` inside `GL n ℝ`, the maximal compact
  subgroup of condition (b2).
* `integralAdeles` and `integralAdelicSubgroup`: the integral adeles `Ẑ` and the compact open
  subgroup `GL n Ẑ` of `G(𝔸_f)` (`isOpen_integralAdelicSubgroup`,
  `isCompact_integralAdelicSubgroup`), which witnesses condition (b1) for constant automorphic
  forms.

## Implementation notes

Compactness of `orthogonalSubgroup n` and its maximality (Cartan-Iwasawa-Malcev, which also
makes it unique up to conjugacy) are asserted in its docstring but not formalised; of
compactness, the boundedness half is proved (`abs_coe_le_one_of_mem_orthogonalSubgroup`).

*References:*
- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*, in Automorphic
  Forms, Representations and L-functions (Corvallis), Proc. Sympos. Pure Math. 33, Part 1,
  Amer. Math. Soc. (1979), 189–207; §4.
-/

namespace Matrix.GeneralLinearGroup

open scoped IsDedekindDomain.FiniteAdeleRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The subgroups `Γ = G(ℚ)` and `K = O n ℝ`: conditions (a) and (b2) -/

variable (n) in
/-- The diagonal embedding of the rational points `G(ℚ) = GL n ℚ` into
`G(𝔸_f) × G(ℝ) = GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ`, through the inclusions of `ℚ` into the finite
adeles and into `ℝ`. -/
noncomputable def diagonalEmbedding : GL n ℚ →* GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ :=
  (map (algebraMap ℚ 𝔸ᶠ[ℤ, ℚ])).prod (map (algebraMap ℚ ℝ))

variable (n) in
/-- The subgroup `Γ = G(ℚ)` of `G(𝔸_f) × G(ℝ)`: the range of the diagonal embedding of
`GL n ℚ`. Condition (a) for an automorphic form is left invariance under this subgroup. -/
noncomputable def ratDiagonal : Subgroup (GL n 𝔸ᶠ[ℤ, ℚ] × GL n ℝ) :=
  (diagonalEmbedding n).range

/-- The orthogonal group `O n ℝ` as a subgroup of `GL n ℝ`: the matrices whose transpose is
their inverse. This is the maximal compact subgroup of `GL n ℝ` — up to conjugacy the only one,
by the Cartan-Iwasawa-Malcev theorem — and it is the `K` of the pair `(G, K)` in the definition
of an automorphic form for `GL n`. -/
def orthogonalSubgroup (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n ℝ) where
  carrier := {y | (y : Matrix n n ℝ)ᵀ = (↑y⁻¹ : Matrix n n ℝ)}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Units.val_mul, Matrix.transpose_mul, ha, hb]
    simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [inv_inv, ← ha, Matrix.transpose_transpose]

@[simp]
lemma mem_orthogonalSubgroup {y : GL n ℝ} :
    y ∈ orthogonalSubgroup n ↔ (y : Matrix n n ℝ)ᵀ = (↑y⁻¹ : Matrix n n ℝ) := Iff.rfl

lemma mem_orthogonalSubgroup_iff_mul_transpose {y : GL n ℝ} :
    y ∈ orthogonalSubgroup n ↔ (y : Matrix n n ℝ) * (y : Matrix n n ℝ)ᵀ = 1 := by
  rw [mem_orthogonalSubgroup]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]; exact y.mul_inv
  · rw [← Matrix.inv_eq_right_inv h, Matrix.GeneralLinearGroup.coe_inv]

/-- The entries of an orthogonal matrix are bounded by `1`: each row is a unit vector. This is
the boundedness half of the compactness of `orthogonalSubgroup n`; see the implementation notes
on what is and is not formalised about that. -/
lemma abs_coe_le_one_of_mem_orthogonalSubgroup {y : GL n ℝ} (hy : y ∈ orthogonalSubgroup n)
    (i j : n) : |(y : Matrix n n ℝ) i j| ≤ 1 := by
  set M := (y : Matrix n n ℝ) with hM
  have hd : ∑ k, M i k * M i k = 1 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrArg (fun A => A i i)
      (mem_orthogonalSubgroup_iff_mul_transpose.mp hy)
  exact abs_le_one_iff_mul_self_le_one.mpr (hd ▸ Finset.single_le_sum
    (f := fun k => M i k * M i k) (fun k _ => mul_self_nonneg _) (Finset.mem_univ j))

/-! ### The compact open subgroup `GL n Ẑ`: condition (b1) -/

section IntegralSubgroup

open IsDedekindDomain RestrictedProduct

set_option backward.isDefEq.respectTransparency false in
/-- The `v`-adic integers of `ℚ` are compact: they are homeomorphic to `ℤ_[p]` for the
corresponding prime `p`. -/
instance (v : HeightOneSpectrum ℤ) : CompactSpace (v.adicCompletionIntegers ℚ) := by
  have : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let _ : Algebra ℤ ↥(v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv
    v).toHomeomorph.symm.compactSpace

instance : T2Space 𝔸ᶠ[ℤ, ℚ] :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum ℤ,
    [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))

/-- The integral adeles `Ẑ = ∏ᵥ ℤᵥ` as a subring of the finite adeles of `ℚ`: the adeles that
are integral at every place. -/
def integralAdeles : Subring 𝔸ᶠ[ℤ, ℚ] where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers ℚ}
  one_mem' _v := one_mem _
  mul_mem' hx hy v := mul_mem (hx v) (hy v)
  zero_mem' _v := zero_mem _
  add_mem' hx hy v := add_mem (hx v) (hy v)
  neg_mem' hx v := neg_mem (hx v)

lemma isOpen_integralAdeles : IsOpen (integralAdeles : Set 𝔸ᶠ[ℤ, ℚ]) :=
  RestrictedProduct.isOpen_forall_mem fun _ => Valued.isOpen_valuationSubring _

lemma isCompact_integralAdeles : IsCompact (integralAdeles : Set 𝔸ᶠ[ℤ, ℚ]) := by
  have h : (integralAdeles : Set 𝔸ᶠ[ℤ, ℚ])
      = Set.range (structureMap (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
          (fun v => v.adicCompletionIntegers ℚ) Filter.cofinite) := by
    rw [range_structureMap]
    rfl
  rw [h, ← Set.image_univ]
  exact (CompactSpace.isCompact_univ
    (X := Π v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ)).image
    isEmbedding_structureMap.continuous

variable (n) in
/-- `GL n Ẑ` inside `GL n 𝔸ᶠ[ℤ, ℚ]`: the matrices whose entries, and whose inverse's entries,
are integral adeles. It is a compact open subgroup of `G(𝔸_f)`
(`isOpen_integralAdelicSubgroup`, `isCompact_integralAdelicSubgroup`), as condition (b1)
requires. -/
def integralAdelicSubgroup : Subgroup (GL n 𝔸ᶠ[ℤ, ℚ]) where
  carrier := {g | (∀ i j, (g : Matrix n n 𝔸ᶠ[ℤ, ℚ]) i j ∈ integralAdeles) ∧
      ∀ i j, (↑g⁻¹ : Matrix n n 𝔸ᶠ[ℤ, ℚ]) i j ∈ integralAdeles}
  one_mem' := by
    have h1 : ∀ i j : n, (1 : Matrix n n 𝔸ᶠ[ℤ, ℚ]) i j ∈ integralAdeles := fun i j => by
      rcases eq_or_ne i j with rfl | h
      · rw [Matrix.one_apply_eq]; exact one_mem _
      · rw [Matrix.one_apply_ne h]; exact zero_mem _
    exact ⟨fun i j => by simpa using h1 i j, fun i j => by simpa using h1 i j⟩
  mul_mem' {a b} ha hb := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun k _ => mul_mem (ha.1 i k) (hb.1 k j)
    · have hrev : ((a * b)⁻¹ : GL n 𝔸ᶠ[ℤ, ℚ]) = b⁻¹ * a⁻¹ := _root_.mul_inv_rev a b
      rw [hrev, Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun k _ => mul_mem (hb.2 i k) (ha.2 k j)
  inv_mem' {a} ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

lemma isOpen_integralAdelicSubgroup :
    IsOpen ((integralAdelicSubgroup n) : Set (GL n 𝔸ᶠ[ℤ, ℚ])) := by
  have hW : IsOpen {M : Matrix n n 𝔸ᶠ[ℤ, ℚ] | ∀ i j, M i j ∈ integralAdeles} := by
    have h : {M : Matrix n n 𝔸ᶠ[ℤ, ℚ] | ∀ i j, M i j ∈ integralAdeles}
        = ⋂ i, ⋂ j, (fun M : Matrix n n 𝔸ᶠ[ℤ, ℚ] => M i j) ⁻¹' integralAdeles := by
      ext M; simp
    rw [h]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_integralAdeles.preimage (continuous_id.matrix_elem i j)
  exact (hW.preimage Units.continuous_val).inter (hW.preimage Units.continuous_coe_inv)

lemma isCompact_integralAdelicSubgroup :
    IsCompact ((integralAdelicSubgroup n) : Set (GL n 𝔸ᶠ[ℤ, ℚ])) := by
  set W : Set (Matrix n n 𝔸ᶠ[ℤ, ℚ]) := {M | ∀ i j, M i j ∈ integralAdeles} with hWdef
  have hWc : IsCompact W :=
    (Set.ext fun M => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩ :
      W = Set.univ.pi fun _ : n => Set.univ.pi fun _ => (integralAdeles : Set 𝔸ᶠ[ℤ, ℚ])) ▸
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_integralAdeles
  have himg : Units.embedProduct _ '' (integralAdelicSubgroup n)
      = (fun p : Matrix n n 𝔸ᶠ[ℤ, ℚ] × Matrix n n 𝔸ᶠ[ℤ, ℚ] => (p.1, MulOpposite.op p.2)) ''
        ((W ×ˢ W) ∩ {p | p.1 * p.2 = 1} ∩ {p | p.2 * p.1 = 1}) := by
    ext p
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(↑g, ↑g⁻¹), ⟨⟨⟨hg.1, hg.2⟩, g.mul_inv⟩, g.inv_mul⟩, rfl⟩
    · rintro ⟨⟨A, B⟩, ⟨⟨⟨hA, hB⟩, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨A, B, h1, h2⟩, ⟨hA, hB⟩, rfl⟩
  rw [Units.isEmbedding_embedProduct.isCompact_iff, himg]
  exact (((hWc.prod hWc).inter_right (isClosed_eq (continuous_fst.mul continuous_snd)
    continuous_const)).inter_right (isClosed_eq (continuous_snd.mul continuous_fst)
      continuous_const)).image
    (continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd))

end IntegralSubgroup

end Matrix.GeneralLinearGroup
