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

public import Mathlib.GroupTheory.Commensurable
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Hecke pairs and their operators

A *Hecke pair* is a group `G` together with a subgroup `K` commensurable with all of its
conjugates. This is exactly the condition under which the double cosets `K \ G / K` act on
the `K`-invariants of any representation of `G`: for a Hecke pair each double coset `K g K`
is a *finite* union of left cosets `x K`, so the operator summing a representation over those
cosets is well defined. No topology and no Haar measure are involved: the operators are
defined by counting cosets, following Shimura, rather than by integrating against a Haar
measure on a locally profinite group.

The motivating example is `G = GL n F` for `F` a nonarchimedean local field and
`K = GL n 𝒪` its maximal compact; there the resulting operators generate the spherical Hecke
algebra whose Satake parameters describe unramified representations.

## Main declarations

* `Subgroup.IsHeckePair`: every conjugate of `K` is commensurable with `K`; equivalently the
  commensurator of `K` is all of `G`.
* `Subgroup.IsHeckePair.finite_image_mk`: a right coset `K g` meets only finitely many left
  cosets, so `K g K` is a finite union of left cosets.
* `Representation.heckeOperator`: the operator of the double coset `K g K` on the
  `K`-invariants of a representation, sending `v` to the sum of `ρ x v` over the left cosets
  `x K` contained in `K g K`.

## Relation to the FLT project

The FLT project has abstract Hecke operators in
`FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Abstract.lean`: for `U V : Subgroup G`
acting on the `U`-invariants of a module, `AbstractHeckeOperator.heckeOperator` is the
operator attached to a double coset, taking the finiteness
`(QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)).Finite`
as a *hypothesis* on each operator. This file supplies that hypothesis rather than assuming
it: `finite_image_mk` is stated in exactly the above form and derived from commensurability,
so for a Hecke pair every Hecke operator exists unconditionally.

*References:*
 - G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Chapter 3
 - [The FLT project](https://github.com/ImperialCollegeLondon/FLT),
   `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Abstract.lean`
-/

open scoped Pointwise

/-! ### Hecke pairs, and the finiteness of their double cosets -/

namespace Subgroup

variable {G : Type*} [Group G]

/-- `K` is a **Hecke subgroup** of `G` when every conjugate of `K` is commensurable with `K`;
equivalently, when the commensurator of `K` is all of `G`.

For such a `K` the double cosets `K \ G / K` carry a convolution product, defined by counting
left cosets; `finite_leftCosets` is the finiteness that makes the count well defined. -/
def IsHeckePair (K : Subgroup G) : Prop :=
  Commensurable.commensurator K = ⊤

theorem isHeckePair_iff {K : Subgroup G} :
    IsHeckePair K ↔ ∀ g : G, Commensurable (ConjAct.toConjAct g • K) K := by
  simp [IsHeckePair, Subgroup.eq_top_iff']

alias ⟨IsHeckePair.commensurable, isHeckePair_of_commensurable⟩ := isHeckePair_iff

/-- To check that `K` is a Hecke subgroup it is enough to bound one of the two relative
indices: the other follows by conjugating by `g⁻¹`. -/
theorem isHeckePair_of_relIndex {K : Subgroup G}
    (hrel : ∀ g : G, (ConjAct.toConjAct g • K).relIndex K ≠ 0) : IsHeckePair K := by
  refine isHeckePair_of_commensurable fun g => ⟨hrel g, ?_⟩
  have key := Subgroup.relIndex_pointwise_smul (h := ConjAct.toConjAct g)
    ((ConjAct.toConjAct g)⁻¹ • K) K
  rw [smul_inv_smul] at key
  rw [key, ← map_inv]
  exact hrel g⁻¹

/-- A normal subgroup is a Hecke subgroup: it is its own conjugates. -/
theorem isHeckePair_of_normal (K : Subgroup G) [K.Normal] : IsHeckePair K :=
  isHeckePair_of_commensurable fun g => by
    rw [(‹K.Normal›).conjAct (ConjAct.toConjAct g)]


namespace IsHeckePair

variable {K : Subgroup G}

/-- For a Hecke pair, the stabiliser in `K` of the coset `g K` is `K ∩ g K g⁻¹`. -/
theorem stabilizer_eq (g : G) :
    MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K) =
      (ConjAct.toConjAct g • K).subgroupOf K := by
  ext ⟨k, hk⟩
  have key : ((⟨k, hk⟩ : K) • (QuotientGroup.mk g : G ⧸ K)) = QuotientGroup.mk (k * g) := rfl
  simp only [MulAction.mem_stabilizer_iff, key, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, ConjAct.ofConjAct_inv,
    ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [show (k * g)⁻¹ * g = (g⁻¹ * k * g)⁻¹ by group]
  exact K.inv_mem_iff

/-- The left cosets met by the right coset `K g` are exactly the `K`-orbit of `g K` in
`G ⧸ K`. -/
theorem image_mk_eq_orbit (g : G) :
    ((QuotientGroup.mk : G → G ⧸ K) '' ((K : Set G) * {g}))
      = MulAction.orbit K (QuotientGroup.mk g : G ⧸ K) := by
  rw [Set.mul_singleton, Set.image_image]
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, hk, rfl⟩

/-- **The finiteness underlying the Hecke algebra.** For a Hecke pair, the right coset `K g`
meets only finitely many left cosets of `K`; equivalently `K g K` is a finite union of left
cosets.

This is stated in the form in which the FLT project's `AbstractHeckeOperator.heckeOperator`
takes it as a hypothesis, so that for a Hecke pair that hypothesis is always available. -/
theorem finite_image_mk (hK : IsHeckePair K) (g : G) :
    ((QuotientGroup.mk : G → G ⧸ K) '' ((K : Set G) * {g})).Finite := by
  have himg := image_mk_eq_orbit (K := K) g
  have hfi : (MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)).FiniteIndex := by
    rw [stabilizer_eq]
    exact ⟨(hK.commensurable g).1⟩
  have : Finite (K ⧸ MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)) :=
    Subgroup.finite_quotient_of_finiteIndex
  rw [himg]
  exact Set.finite_coe_iff.mp
    (Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer K
      (QuotientGroup.mk g : G ⧸ K)).symm)

end IsHeckePair

end Subgroup

/-! ### The Hecke operator on the `K`-invariants of a representation

For a Hecke pair `(G, K)` and a representation `ρ` of `G`, the Hecke operator attached to
`g : G` sends a `K`-invariant vector `v` to the sum of `ρ x v` over the finitely many left
cosets `x K` contained in the double coset `K g K`. Unlike the corresponding construction in
the FLT project, no finiteness hypothesis is carried: it is supplied by
`Subgroup.IsHeckePair.finite_image_mk`. -/

namespace Representation

variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
variable (ρ : Representation R G V) (K : Subgroup G)

/-- The `K`-invariants of `ρ`. -/
noncomputable abbrev subgroupInvariants : Submodule R V :=
  Representation.invariants (ρ.comp K.subtype)

variable {ρ K}

theorem mem_subgroupInvariants {v : V} :
    v ∈ ρ.subgroupInvariants K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩

/-- A `K`-invariant vector may be translated by a coset representative: `ρ x v` depends only on
`x K`. This is the function on `G ⧸ K` that the Hecke operator sums. -/
noncomputable def translateOn (v : ρ.subgroupInvariants K) : G ⧸ K → V :=
  Quotient.lift (fun x : G => ρ x (v : V)) <| by
    intro a b hab
    have hK : a⁻¹ * b ∈ K := by simpa [QuotientGroup.leftRel_apply] using hab
    have := (mem_subgroupInvariants.mp v.2) _ hK
    calc ρ a (v : V) = ρ a (ρ (a⁻¹ * b) (v : V)) := by rw [this]
      _ = ρ b (v : V) := by rw [← Module.End.mul_apply, ← map_mul]; group

@[simp]
theorem translateOn_mk (v : ρ.subgroupInvariants K) (x : G) :
    translateOn v (QuotientGroup.mk x) = ρ x (v : V) := rfl

theorem translateOn_smul (v : ρ.subgroupInvariants K) (k : K) (c : G ⧸ K) :
    translateOn v (k • c) = ρ k (translateOn v (c : G ⧸ K)) := by
  induction c using QuotientGroup.induction_on with
  | _ x =>
    show translateOn v (QuotientGroup.mk ((k : G) * x)) = _
    simp [map_mul]

theorem smul_mem_orbit_of_mem {x : G ⧸ K} {c : G ⧸ K} (hc : c ∈ MulAction.orbit K x) (k : K) :
    k • c ∈ MulAction.orbit K x := by
  obtain ⟨k', rfl⟩ := hc
  exact ⟨k * k', mul_smul k k' x⟩

variable (ρ K)

/-- **The Hecke operator** attached to `g : G`, acting on the `K`-invariants of `ρ`: it sends a
`K`-invariant vector `v` to the sum of `ρ x v` over the left cosets `x K` making up the double
coset `K g K`.

No finiteness hypothesis is needed: it comes from `Subgroup.IsHeckePair.finite_image_mk`. -/
noncomputable def heckeOperator (hK : K.IsHeckePair) (g : G) :
    ρ.subgroupInvariants K →ₗ[R] ρ.subgroupInvariants K where
  toFun v := ⟨∑ c ∈ (hK.finite_image_mk g).toFinset, translateOn v c, by
    rw [mem_subgroupInvariants]
    intro k hk
    rw [map_sum]
    refine Finset.sum_nbij' (i := fun c => (⟨k, hk⟩ : K) • c)
      (j := fun c => (⟨k, hk⟩ : K)⁻¹ • c) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Set.Finite.mem_toFinset, Subgroup.IsHeckePair.image_mk_eq_orbit] at hc ⊢
      exact smul_mem_orbit_of_mem hc _
    · intro c hc
      simp only [Set.Finite.mem_toFinset, Subgroup.IsHeckePair.image_mk_eq_orbit] at hc ⊢
      exact smul_mem_orbit_of_mem hc _
    · intro c _; simp
    · intro c _; simp
    · intro c _; rw [translateOn_smul]⟩
  map_add' v w := by
    ext
    simp only [Submodule.coe_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | _ x => simp [translateOn]
  map_smul' r v := by
    ext
    simp only [RingHom.id_apply, SetLike.val_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    induction c using QuotientGroup.induction_on with
    | _ x => simp [translateOn]

/-- The Hecke operator at the identity is the identity: the double coset `K 1 K` is a single
left coset. -/
@[simp]
theorem heckeOperator_one (hK : K.IsHeckePair) :
    heckeOperator ρ K hK 1 = LinearMap.id := by
  ext v
  have hsingleton : (hK.finite_image_mk 1).toFinset = {(QuotientGroup.mk 1 : G ⧸ K)} := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mul_singleton, Set.image_image, mul_one,
      Set.mem_image, Finset.mem_singleton, SetLike.mem_coe]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact QuotientGroup.eq.mpr (by simpa using inv_mem hk)
    · rintro rfl
      exact ⟨1, one_mem K, rfl⟩
  simp only [heckeOperator, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq,
    Submodule.coe_mk, hsingleton, Finset.sum_singleton]
  show translateOn v (QuotientGroup.mk 1) = (v : V)
  simp

end Representation
