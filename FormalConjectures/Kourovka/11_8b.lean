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
# Conjecture 11.8(b)

by Ya. G. Berkovich

*Reference:* [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v49)

-/

@[expose] public section

namespace Kourovka.«11.8b»
open CategoryTheory

/-- The irreducible complex characters of $G$, viewed as functions $G \to \mathbb{C}$. -/
def Irr₁ (G : Type) [Group G]: Set (G → ℂ)
  := {χ:  G → ℂ  | ∃ V :  FDRep ℂ G, Simple V ∧ χ = V.character }

/-- The irreducible complex characters of $G$ and $H$ have the same degrees, with multiplicities.
The bijection matches characters and preserves their values at the identity. -/
def SameDegrees (G : Type) [Group G] (H: Type) [Group H] :=
  ∃ bij: Irr₁ G ≃ Irr₁ H, ∀ χ : Irr₁ G, (bij χ).val 1 = χ.val 1

/-- Let $G$ and $H$ be finite groups with the same multiset of irreducible complex
character degrees.
Is $H$ soluble whenever $G$ is soluble? -/
@[category research open, question, AMS 20]
theorem kourovka_11_8b : ∀ (G : Type) [Group G] [Finite G] (H : Type) [Group H] [Finite H],
  SameDegrees G H → Group.IsSolvable G → Group.IsSolvable H := by sorry

/-- Let $G$ and $H$ be finite groups whose complex group algebras are isomorphic as
$\mathbb{C}$-algebras. Is $H$ soluble whenever $G$ is soluble?
This is the group-algebra formulation of Kourovka Problem 11.8(b). -/
@[category research open, question, AMS 20]
theorem kourovka_11_8b': ∀  (G : Type) [Group G] [Finite G] (H: Type) [Group H] [Finite H],
  Nonempty (MonoidAlgebra ℂ G≃ₐ[ℂ] MonoidAlgebra ℂ H) →
  Group.IsSolvable G → Group.IsSolvable H := by sorry

/-
## Equivalence of the two formulations

We aim to prove that the statements of `kourovka_11_8b` and `kourovka_11_8b'` are equivalent.
-/

/-- In a decomposition of $\mathbb{C}[G]$ into nonzero full matrix algebras, the block indices
correspond bijectively to the irreducible complex characters of $G$.
The size of each block is the degree of its corresponding character.
The nonzero-size hypothesis excludes empty matrix blocks. -/
@[category textbook, AMS 20]
theorem irr_equiv_blocks (G : Type) [Group G] [Finite G] (n : ℕ)
  (d : Fin n → ℕ)(hd : ∀ i, NeZero (d i)):
  Nonempty (MonoidAlgebra ℂ G ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
  → ∃ bij : Fin n ≃ Irr₁ G, ∀ i, (bij i).val 1 = d i  := by sorry

/-- Reordering matrix factors along a bijection that preserves their sizes gives an equivalence
of the product algebras over $\mathbb{C}$. -/
@[category textbook, AMS 20]
lemma reindex (n m :ℕ) (d : Fin n → ℕ) (d' : Fin m → ℕ) (σ : Fin n ≃ Fin m): (∀ i, d' (σ i) = d i)
  → Nonempty ( (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    ≃ₐ[ℂ]  (Π j, Matrix (Fin (d' j)) (Fin (d' j)) ℂ)) := by
  intro hi
  obtain rfl : d' ∘ σ = d := by
    funext i
    exact hi i
  exact ⟨(AlgEquiv.piCongrLeft ℂ (fun j => Matrix (Fin (d' j)) (Fin (d' j)) ℂ) σ)⟩

/-- Two finite groups have the same multiset of irreducible complex character degrees if and only
if their complex group algebras are isomorphic as $\mathbb{C}$-algebras. -/
@[category textbook, AMS 20]
theorem sameDegrees_iff_algEquiv (G : Type) [Group G] [Finite G]
  (H: Type) [Group H] [Finite H] : SameDegrees G H
  ↔ Nonempty (MonoidAlgebra ℂ G≃ₐ[ℂ] MonoidAlgebra ℂ H) := by
      obtain ⟨n, d, hd, ⟨g⟩⟩ :=
        IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
      obtain ⟨eG, hG⟩ := irr_equiv_blocks G n d hd ⟨g⟩
      constructor
      · rintro ⟨bij, hbij⟩
        obtain ⟨m, d', hd', ⟨h⟩⟩ :=
          IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ H)
        obtain ⟨eH, hH⟩ := irr_equiv_blocks H m d' hd' ⟨h⟩
        let σ := (eG.trans bij).trans eH.symm
        have hσ : ∀ i, d' (σ i) = d i := by
          intro i
          specialize hG i
          specialize hH (σ i)
          simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply] at hH
          rw [←hbij (eG i), hH] at hG
          norm_cast at hG
        obtain ⟨f⟩ := reindex n m d d' σ hσ
        exact ⟨(g.trans f).trans h.symm⟩
      · rintro ⟨f⟩
        obtain ⟨eH, hH⟩ := irr_equiv_blocks H n d hd ⟨f.symm.trans g⟩
        use eG.symm.trans eH
        intro χ
        specialize hG (eG.symm χ)
        specialize hH (eG.symm χ)
        rw [Equiv.apply_symm_apply] at hG
        rw [hG]
        exact hH

/-- The statements of `kourovka_11_8b` and `kourovka_11_8b'` are equivalent. -/
@[category test, AMS 20]
example : (type_of% kourovka_11_8b) ↔ (type_of% kourovka_11_8b') := by
  simp_rw +contextual [sameDegrees_iff_algEquiv]
end Kourovka.«11.8b»
