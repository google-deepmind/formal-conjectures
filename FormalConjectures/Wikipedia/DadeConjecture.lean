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

import FormalConjectures.Util.ProblemImports

/-!
# Dade's Conjectures

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Dade_conjecture)

The block-theoretic prerequisites (Brauer blocks, defect groups, character defects,
Brauer correspondence) are not in Mathlib, so we use opaque placeholders.
-/

namespace Dade

/-- The condition `O_p(G) = 1`: every normal `p`-subgroup of `G` is trivial. This is
a standing hypothesis in Dade's ordinary conjecture. -/
def HasTrivialPCore (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∀ N : Subgroup G, N.Normal → IsPGroup p N → N = ⊥

/-- The (finite) type of `p`-blocks of `G`. Placeholder. -/
@[reducible] def BrauerBlock (G : Type*) [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    Type := PUnit

instance {G : Type*} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] :
    Fintype (BrauerBlock G p) := PUnit.fintype

/-- The defect of a `p`-block. -/
noncomputable def BrauerBlock.defect {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] : BrauerBlock G p → ℕ := fun _ => sorry

/-- A strictly ascending `p`-chain of `G` starting at the trivial subgroup. -/
structure PChain (G : Type*) [Group G] (p : ℕ) where
  length : ℕ
  group : Fin (length + 1) → Subgroup G
  group_zero : group 0 = ⊥
  isPGroup : ∀ i, IsPGroup p (group i)
  strictMono : StrictMono group

/-- A `G`-conjugacy class of `p`-chains. -/
opaque PChainClass (G : Type*) [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    Type := PUnit

noncomputable instance (G : Type*) [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    Fintype (PChainClass G p) := sorry

/-- The length of (any representative of) a chain class. -/
noncomputable def PChainClass.length {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] : PChainClass G p → ℕ := fun _ => sorry

/-- The number of ordinary irreducible characters of defect `d` summed over those
blocks of `N_G(σ)` that are Brauer-correspondent to `B`. -/
noncomputable def PChainClass.kBrauer {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] (_σ : PChainClass G p) (_B : BrauerBlock G p) (_d : ℕ) : ℕ :=
  sorry

/--
**Dade's ordinary conjecture** [Dade 1992].

For a finite group `G` with `O_p(G) = 1`, a `p`-block `B` of positive defect, and any
`d ≥ 0`, the alternating sum over `G`-conjugacy classes of `p`-chains vanishes.
-/
@[category research open, AMS 16 20]
theorem dade_ordinary (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) [Fact p.Prime] (hG : HasTrivialPCore G p)
    (B : BrauerBlock G p) (hB : 0 < B.defect) (d : ℕ) :
    (∑ σ : PChainClass G p, (-1 : ℤ) ^ σ.length * (σ.kBrauer B d : ℤ)) = 0 := by
  sorry

/-- The (opaque) finite indexing type of ordinary irreducible characters of `H`. -/
opaque IrrChar (H : Type*) [Group H] : Type := PUnit

noncomputable instance (H : Type*) [Group H] : Fintype (IrrChar H) := sorry

/-- An irreducible character of a normal subgroup is `G`-invariant. -/
opaque IrrChar.IsGInvariant {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (θ : IrrChar N) : Prop := True

/-- Count of defect-`d` characters in the Brauer correspondent of `B` lying above `θ`. -/
noncomputable def PChainClass.kBrauerAbove {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] (_σ : PChainClass G p) (_B : BrauerBlock G p)
    {N : Subgroup G} (_hN : N.Normal) (_θ : IrrChar N) (_d : ℕ) : ℕ := sorry

/--
**Dade's invariant conjecture** [Dade 1994].

The alternating sum vanishes when characters are filtered to those lying above a
`G`-stable irreducible character `θ` of a normal subgroup `N`.
-/
@[category research open, AMS 16 20]
theorem dade_invariant (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) [Fact p.Prime] (hG : HasTrivialPCore G p)
    (B : BrauerBlock G p) (hB : 0 < B.defect)
    {N : Subgroup G} (hN : N.Normal) (θ : IrrChar N)
    (hθ : IrrChar.IsGInvariant hN θ) (d : ℕ) :
    (∑ σ : PChainClass G p,
        (-1 : ℤ) ^ σ.length * (σ.kBrauerAbove B hN θ d : ℤ)) = 0 := by
  sorry

/-- A finite central cover of `G`. -/
structure CentralCover (G : Type*) [Group G] where
  Hat : Type
  [toGroup : Group Hat]
  [toFintype : Fintype Hat]
  proj : Hat →* G
  surjective : Function.Surjective proj
  ker_central : proj.ker ≤ Subgroup.center Hat

/-- Opaque indexing type for irreducible characters of the central kernel. -/
opaque CentralCover.IrrCenterChar {G : Type*} [Group G] (E : CentralCover G) :
    Type := PUnit

noncomputable instance {G : Type*} [Group G] (E : CentralCover G) :
    Fintype E.IrrCenterChar := sorry

/-- Count of defect-`d` characters in the lifted Brauer correspondent with central
character `λ`. -/
noncomputable def PChainClass.kBrauerCentral {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] (_σ : PChainClass G p) (_B : BrauerBlock G p)
    (E : CentralCover G) (_lam : E.IrrCenterChar) (_d : ℕ) : ℕ := sorry

/--
**Dade's projective conjecture** [Dade 1994].

The alternating sum vanishes for any finite central cover `Ĝ → G` and any irreducible
character `λ` of the central kernel.
-/
@[category research open, AMS 16 20]
theorem dade_projective (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) [Fact p.Prime] (hG : HasTrivialPCore G p)
    (B : BrauerBlock G p) (hB : 0 < B.defect)
    (E : CentralCover G) (lam : E.IrrCenterChar) (d : ℕ) :
    (∑ σ : PChainClass G p,
        (-1 : ℤ) ^ σ.length * (σ.kBrauerCentral B E lam d : ℤ)) = 0 := by
  sorry

/-- A `p'`-element: an element whose order is coprime to `p`. -/
def IsPRegular {G : Type*} [Group G] (p : ℕ) (g : G) : Prop :=
  Nat.Coprime (orderOf g) p

/-- Count of defect-`d` characters whose Isaacs–Navarro `p'`-class is the class of `c`. -/
noncomputable def PChainClass.kBrauerIN {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] (_σ : PChainClass G p) (_B : BrauerBlock G p)
    (_c : G) (_d : ℕ) : ℕ := sorry

/--
**Uno's refinement of Dade's conjecture** [Uno 2004], building on [Isaacs–Navarro 2002].

The alternating sum vanishes after refining the count by the `p'`-class of the
relevant character, parametrised by a `p`-regular element `c ∈ G`.
-/
@[category research open, AMS 16 20]
theorem dade_uno_refinement (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (p : ℕ) [Fact p.Prime] (hG : HasTrivialPCore G p)
    (B : BrauerBlock G p) (hB : 0 < B.defect)
    (c : G) (hc : IsPRegular p c) (d : ℕ) :
    (∑ σ : PChainClass G p,
        (-1 : ℤ) ^ σ.length * (σ.kBrauerIN B c d : ℤ)) = 0 := by
  sorry

end Dade