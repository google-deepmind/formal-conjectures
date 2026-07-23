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

public import FormalConjecturesForMathlib.Combinatorics.Basic
public import Mathlib.Combinatorics.Additive.Convolution

@[expose] public section

/-!
# Representation counts for sumsets

This file defines the ordered representation count `Finset.repCount` and the uniform lower-bound
predicate `Finset.MinRep`. It also relates these notions to sets without unique sums and proves the
multiplicativity lemma used in the Łuczak–Schoen construction.

Reference:
- [LS08] Łuczak, Tomasz and Schoen, Tomasz. "On the number of unique sums."
-/

open Finset
open scoped Pointwise

namespace Finset

variable {α : Type*} [AddCommMonoid α] [DecidableEq α]

/--
`repCount A g` is the number of *ordered* pairs `(a, b) ∈ A × A` with `a + b = g`.
This is `ν` in [LS08] (p. 101) and `r_A` in [Be23].
-/
def repCount (A : Finset α) (g : α) : ℕ :=
  ((A ×ˢ A).filter fun q => q.1 + q.2 = g).card

/-- Over an additive group, `repCount A` is `Finset.addConvolution` applied to `A` and itself.
(`repCount` itself only requires an additive commutative monoid, matching
`HasNoUniqueRepresentation`.) -/
theorem repCount_eq_addConvolution {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (g : G) : repCount A g = A.addConvolution A g := rfl

/--
`MinRep A k` says every element of the sumset `A + A` has at least `k` ordered
representations as a sum of two elements of `A`.
-/
def MinRep (A : Finset α) (k : ℕ) : Prop :=
  ∀ g ∈ A + A, k ≤ repCount A g

/--
The bridge to the repo's predicate: an element with `≤ 2` ordered representations
is exactly a "unique sum" up to order (`r = 1` is the diagonal `a + a`; `r = 2` is
`a + b, b + a` with `a ≠ b`), so `3` ordered representations everywhere means no
unique sums at all.
-/
theorem hasNoUniqueRepresentation_of_minRep_three {A : Finset α} (h : MinRep A 3) :
    HasNoUniqueRepresentation A := by
  rw [HasNoUniqueRepresentation, Set.eq_empty_iff_forall_notMem]
  intro n hn
  rcases hn with ⟨q, hq₁, hq₂, hqsum, huniq⟩
  have hnadd : n ∈ A + A := Finset.mem_add.mpr ⟨q.1, hq₁, q.2, hq₂, hqsum⟩
  have hthree : 3 ≤ repCount A n := h n hnadd
  have hsubset : ((A ×ˢ A).filter fun r ↦ r.1 + r.2 = n) ⊆ {q, q.swap} := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_product] at hr
    rcases huniq r.1 hr.1.1 r.2 hr.1.2 hr.2 with hqr | hqr
    · exact Finset.mem_insert.mpr (.inl (Prod.ext hqr.1 hqr.2))
    · refine Finset.mem_insert.mpr (.inr (Finset.mem_singleton.mpr ?_))
      apply Prod.ext
      · exact hqr.1
      · exact hqr.2
  have htwo : repCount A n ≤ 2 := by
    calc
      repCount A n ≤ ({q, q.swap} : Finset (α × α)).card := by
        simpa only [repCount] using Finset.card_le_card hsubset
      _ ≤ 2 := by
        simpa only [Finset.card_singleton, Nat.reduceAdd] using
          Finset.card_insert_le q ({q.swap} : Finset (α × α))
  omega

/--
[LS08, Lemma 5], multiplicativity of the representation count. The hypothesis
`(A + B).card = A.card * B.card` (the addition map `A × B → A + B` is a bijection)
is essential: the statement is FALSE without it. [LS08] obtain it from Lemma 4.
-/
theorem MinRep.add {A B : Finset α} {k l : ℕ}
    (hA : MinRep A k) (hB : MinRep B l)
    (hcard : (A + B).card = A.card * B.card) :
    MinRep (A + B) (k * l) := by
  have hadd : Set.InjOn (fun q : α × α ↦ q.1 + q.2) (A ×ˢ B) :=
    Finset.card_add_iff.mp hcard
  intro g hg
  rcases Finset.mem_add.mp hg with ⟨u, hu, v, hv, huv⟩
  rcases Finset.mem_add.mp hu with ⟨a₁, ha₁, b₁, hb₁, hab₁⟩
  rcases Finset.mem_add.mp hv with ⟨a₂, ha₂, b₂, hb₂, hab₂⟩
  let RA := ((A ×ˢ A).filter fun q ↦ q.1 + q.2 = a₁ + a₂)
  let RB := ((B ×ˢ B).filter fun q ↦ q.1 + q.2 = b₁ + b₂)
  let RAB := (((A + B) ×ˢ (A + B)).filter fun q ↦ q.1 + q.2 = g)
  have hmap : Set.MapsTo
      (fun q : (α × α) × (α × α) ↦ (q.1.1 + q.2.1, q.1.2 + q.2.2))
      ↑(RA ×ˢ RB) RAB := by
    intro q hq
    simp only [RA, RB, RAB, Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hq ⊢
    refine ⟨⟨Finset.add_mem_add hq.1.1.1 hq.2.1.1,
      Finset.add_mem_add hq.1.1.2 hq.2.1.2⟩, ?_⟩
    calc
      (q.1.1 + q.2.1) + (q.1.2 + q.2.2) =
          (q.1.1 + q.1.2) + (q.2.1 + q.2.2) := by ac_rfl
      _ = (a₁ + a₂) + (b₁ + b₂) := by rw [hq.1.2, hq.2.2]
      _ = (a₁ + b₁) + (a₂ + b₂) := by ac_rfl
      _ = u + v := by rw [hab₁, hab₂]
      _ = g := huv
  have hinj : Set.InjOn
      (fun q : (α × α) × (α × α) ↦ (q.1.1 + q.2.1, q.1.2 + q.2.2))
      ↑(RA ×ˢ RB) := by
    intro q hq q' hq' heq
    simp only [RA, RB, Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hq hq'
    have hq₁ : (q.1.1, q.2.1) ∈ (↑A : Set α) ×ˢ (↑B : Set α) :=
      Set.mk_mem_prod hq.1.1.1 hq.2.1.1
    have hq₁' : (q'.1.1, q'.2.1) ∈ (↑A : Set α) ×ˢ (↑B : Set α) :=
      Set.mk_mem_prod hq'.1.1.1 hq'.2.1.1
    have hq₂ : (q.1.2, q.2.2) ∈ (↑A : Set α) ×ˢ (↑B : Set α) :=
      Set.mk_mem_prod hq.1.1.2 hq.2.1.2
    have hq₂' : (q'.1.2, q'.2.2) ∈ (↑A : Set α) ×ˢ (↑B : Set α) :=
      Set.mk_mem_prod hq'.1.1.2 hq'.2.1.2
    have h₁ : (q.1.1, q.2.1) = (q'.1.1, q'.2.1) :=
      hadd hq₁ hq₁' (congrArg Prod.fst heq)
    have h₂ : (q.1.2, q.2.2) = (q'.1.2, q'.2.2) :=
      hadd hq₂ hq₂' (congrArg Prod.snd heq)
    ext <;> simp_all
  have hle : (RA ×ˢ RB).card ≤ RAB.card :=
    Finset.card_le_card_of_injOn _ hmap hinj
  change k * l ≤ RAB.card
  calc
    k * l ≤ RA.card * RB.card := Nat.mul_le_mul
      (hA (a₁ + a₂) (Finset.add_mem_add ha₁ ha₂))
      (hB (b₁ + b₂) (Finset.add_mem_add hb₁ hb₂))
    _ = (RA ×ˢ RB).card := (Finset.card_product RA RB).symm
    _ ≤ RAB.card := hle

end Finset
