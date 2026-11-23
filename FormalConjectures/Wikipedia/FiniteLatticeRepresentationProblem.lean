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
# Finite lattice representation problem

Grätzer and Schmidt (1963) showed that algebraic lattices coincide up to isomorphism with
congruence lattices of universal algebras. Restricting to finite carriers asks if every finite
nonempty lattice $L$ can be realized as $\operatorname{Con}(A)$ for a finite algebra $A$.

This module formalises the equivalent subgroup-interval formulation established by Pálfy and
Pudlák [PP80]: every finite nonempty lattice $L$ arises as $\operatorname{Con}(A)$ for a finite
algebra $A$ precisely when every finite nonempty lattice $L$ embeds isomorphically onto a subgroup
interval $[H, K]$ inside $\operatorname{Sub}(G)$ for a finite group $G$, or equivalently onto an
upper subgroup interval $[H, \top]$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Finite_lattice_representation_problem)
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Algebra)
- [PP80] P. P. Pálfy and P. Pudlák, *Congruence lattices of finite algebras and intervals in
  subgroup lattices of finite groups*, Algebra Universalis **11** (1980), no. 1, 22–27,
  [DOI 10.1007/BF02483080](https://doi.org/10.1007/BF02483080).
-/

@[expose] public section

namespace FiniteLatticeRepresentationProblem

/-- A lattice `L` is representable as a finite-group subgroup interval if there exist a finite
group `G` and subgroups `H ≤ K` of `G` with `L` order-isomorphic to `Set.Icc H K`. -/
def IsSubgroupLatticeInterval (L : Type*) [Lattice L] : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G) (H K : Subgroup G),
    H ≤ K ∧ Nonempty (L ≃o Set.Icc H K)

/-- An empty `Lattice` cannot be order-isomorphic to `Set.Icc H K` when `H ≤ K`, because `H`
always belongs to `Set.Icc H K`. -/
@[category test, AMS 6 20]
theorem not_isSubgroupLatticeInterval_empty : ¬ IsSubgroupLatticeInterval Empty := by
  rintro ⟨G, hGrp, _, H, K, hHK, ⟨e⟩⟩
  let _ : Group G := hGrp
  exact isEmptyElim (e.symm ⟨H, le_rfl, hHK⟩)

/-- The $1$-element lattice `Unit` is order-isomorphic to the singleton subgroup interval
$[\bot, \bot]$ of `Multiplicative (ZMod 1)`. -/
@[category test, AMS 6 20]
theorem isSubgroupLatticeInterval_unit : IsSubgroupLatticeInterval Unit := by
  refine ⟨Multiplicative (ZMod 1), inferInstance, inferInstance, ⊥, ⊥, le_rfl, ⟨?_⟩⟩
  exact
    { toFun := fun _ => ⟨⊥, le_rfl, le_rfl⟩
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun ⟨M, h1, h2⟩ => Subtype.ext (le_antisymm h1 h2)
      map_rel_iff' := by simp }

/-- The $2$-element lattice `Bool` is order-isomorphic to `Set.Icc ⊥ ⊤` inside
`Multiplicative (ZMod 2)`. -/
@[category test, AMS 6 20]
theorem isSubgroupLatticeInterval_bool : IsSubgroupLatticeInterval Bool := by
  let G := Multiplicative (ZMod 2)
  let g₁ : G := Multiplicative.ofAdd (1 : ZMod 2)
  have hg₁_ne : g₁ ≠ 1 := by decide
  have hnot_le : ¬ ((⊤ : Subgroup G) ≤ ⊥) := fun h =>
    hg₁_ne (Subgroup.mem_bot.mp (h (Subgroup.mem_top g₁)))
  let f : Bool → Set.Icc (⊥ : Subgroup G) ⊤ :=
    fun b => if b then ⟨⊤, bot_le, le_rfl⟩ else ⟨⊥, le_rfl, bot_le⟩
  have hf_bij : Function.Bijective f := by
    refine ⟨fun b₁ b₂ h => ?_, fun ⟨M, _, _⟩ => ?_⟩
    · cases b₁ <;> cases b₂
      · rfl
      · exact (hnot_le (congrArg Subtype.val h).symm.le).elim
      · exact (hnot_le (congrArg Subtype.val h).le).elim
      · rfl
    · have hcases : ∀ x : G, x = 1 ∨ x = g₁ := fun x => by
        obtain ⟨z, rfl⟩ := Multiplicative.ofAdd.surjective x
        fin_cases z <;> [exact Or.inl rfl; exact Or.inr rfl]
      by_cases h1 : g₁ ∈ M
      · refine ⟨true, Subtype.ext ?_⟩
        ext x
        simp only [f, ↓reduceIte, Subgroup.mem_top, true_iff]
        rcases hcases x with rfl | rfl <;> [exact M.one_mem; exact h1]
      · refine ⟨false, Subtype.ext ?_⟩
        ext x
        simp only [f, Bool.false_eq_true, ↓reduceIte, Subgroup.mem_bot]
        refine ⟨fun hx => hx ▸ M.one_mem, fun hxM => ?_⟩
        rcases hcases x with rfl | rfl <;> [rfl; exact False.elim (h1 hxM)]
  refine ⟨G, inferInstance, inferInstance, ⊥, ⊤, bot_le,
    ⟨{ toEquiv := Equiv.ofBijective f hf_bij, map_rel_iff' := ?_ }⟩⟩
  intro a b
  change (f a : Subgroup G) ≤ (f b : Subgroup G) ↔ a ≤ b
  cases a <;> cases b
  · simp [f]
  · simp [f]
  · exact ⟨fun h => (hnot_le h).elim, fun h => absurd h (by decide)⟩
  · simp [f]

/-- The infinite lattice $\mathbb{N}$ cannot be order-isomorphic to `Set.Icc H K` for any finite
group $G$. -/
@[category test, AMS 6 20]
theorem not_isSubgroupLatticeInterval_nat : ¬ IsSubgroupLatticeInterval ℕ := by
  rintro ⟨G, hGrp, hFin, H, K, _, ⟨e⟩⟩
  let _ : Group G := hGrp
  have _ : Finite G := hFin
  have _ : Finite (Subgroup G) := Finite.of_injective (fun M : Subgroup G => (M : Set G))
    SetLike.coe_injective
  exact Infinite.not_finite (Finite.of_injective e e.injective)

/-- Every subgroup interval `Set.Icc H K` of a finite group `G` is order-isomorphic to the upper
subgroup interval `Set.Icc (H.subgroupOf K) ⊤` of the finite group `K`, so
`IsSubgroupLatticeInterval L` is equivalent to realizing `L` as an upper subgroup interval. -/
@[category API, AMS 6 20]
theorem isSubgroupLatticeInterval_iff_exists_Icc_top (L : Type*) [Lattice L] :
    IsSubgroupLatticeInterval L ↔
      ∃ (G : Type) (_ : Group G) (_ : Finite G) (H : Subgroup G),
        Nonempty (L ≃o Set.Icc H ⊤) := by
  constructor
  · rintro ⟨G, hGrp, hFin, H, K, hHK, ⟨e⟩⟩
    let _ : Group G := hGrp
    have _ : Finite G := hFin
    refine ⟨K, inferInstance, inferInstance, H.subgroupOf K, ⟨e.trans ?_⟩⟩
    refine
      { toFun := fun M => ⟨M.1.subgroupOf K, Subgroup.subgroupOf_mono K M.2.1, le_top⟩
        invFun := fun M' =>
          ⟨M'.1.map K.subtype,
            le_trans (by simpa [Subgroup.map_subgroupOf_eq_of_le hHK] using
              Subgroup.map_mono (f := K.subtype) M'.2.1) le_rfl,
            K.map_subtype_le M'.1⟩
        left_inv := fun M => Subtype.ext (Subgroup.map_subgroupOf_eq_of_le M.2.2)
        right_inv := fun M' => Subtype.ext (Subgroup.comap_map_eq_self_of_injective
          Subtype.val_injective M'.1)
        map_rel_iff' := fun {M₁ M₂} => by
          dsimp
          constructor
          · intro h
            have hmap := Subgroup.map_mono (f := K.subtype) h
            rwa [Subgroup.map_subgroupOf_eq_of_le M₁.2.2,
              Subgroup.map_subgroupOf_eq_of_le M₂.2.2] at hmap
          · exact Subgroup.subgroupOf_mono K }
  · rintro ⟨G, hGrp, hFin, H, ⟨e⟩⟩
    let _ : Group G := hGrp
    exact ⟨G, hGrp, hFin, H, ⊤, le_top, ⟨e⟩⟩

/-- **Finite lattice representation problem** (Pálfy–Pudlák subgroup-interval form [PP80]). Is
every finite nonempty lattice $L$ order-isomorphic to `Set.Icc H K` inside $\operatorname{Sub}(G)$
for some finite group $G$? Lean's `Lattice` typeclass permits an empty carrier, so `[Nonempty L]`
is included to match standard mathematical lattices. -/
@[category research open, question, AMS 6 20]
theorem finite_lattice_representation_problem :
    ∀ (L : Type) [Lattice L] [Finite L] [Nonempty L], IsSubgroupLatticeInterval L := by
  sorry

/-- **Upper-interval variant** ([PP80]; see `isSubgroupLatticeInterval_iff_exists_Icc_top`). Is
every finite nonempty lattice $L$ order-isomorphic to the overgroup interval `Set.Icc H ⊤` for
some finite group $G$ and subgroup $H \le G$? (Stated in [PP80] rather than on Wikipedia.) -/
@[category research open, question, AMS 6 20]
theorem finite_lattice_representation_problem.variants.upper_interval :
    ∀ (L : Type) [Lattice L] [Finite L] [Nonempty L],
      ∃ (G : Type) (_ : Group G) (_ : Finite G) (H : Subgroup G),
        Nonempty (L ≃o Set.Icc H ⊤) := by
  sorry

end FiniteLatticeRepresentationProblem
