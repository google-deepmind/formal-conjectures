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
# Erdős Problem 1128

*Reference:* [erdosproblems.com/1128](https://www.erdosproblems.com/1128)
-/

open Cardinal Set Ordinal Order

namespace Erdos1128

/-- A subset $A_1 \times B_1 \times C_1$ of $A \times B \times C$ is **monochromatic**
under a 2-colouring $f : A \to B \to C \to \operatorname{Fin} 2$ if $f$ is constant on
$A_1 \times B_1 \times C_1$. -/
def IsMonochromaticBox {A B C : Type*} (f : A → B → C → Fin 2)
    (A₁ : Set A) (B₁ : Set B) (C₁ : Set C) : Prop :=
  ∃ c : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ c' ∈ C₁, f a b c' = c

/-
Auxiliary lemmas for the Prikry–Mills construction.
These establish key countability and boundedness properties of ω₁.
-/

-- TODO(mo271 review): replace this private `Omega1` abbreviation with a direct use of
-- Mathlib's `ω₁` (e.g. `(ω₁ : Ordinal).toType`), and inline the wrapper lemmas below
-- (`card_le_aleph0_of_lt_omega1`, `countable_toType_of_lt_omega1`,
-- `countable_Iio_of_lt_omega1`, `countable_Iio_omega1`, `countable_subset_bdd`) at the
-- use sites. The current wrappers are thin shims around existing Mathlib API; making
-- the switch is non-trivial because mixing `ω₁` and `(ℵ_ 1).ord` triggers definitional
-- equality issues even though `ord_aleph 1 : (ℵ_ 1).ord = ω_ 1`. Left as a follow-up.

private abbrev Omega1 := {o : Ordinal.{0} // o < (aleph 1).ord}

/-- Any ordinal below ω₁ has countable cardinality. -/
private lemma card_le_aleph0_of_lt_omega1 {γ : Ordinal} (hγ : γ < (aleph 1).ord) :
    γ.card ≤ ℵ₀ := by
  have h : γ.card < aleph 1 := by
    have := (isInitial_ord (aleph 1)).card_lt_card.mpr hγ; simp at this; exact this
  apply not_lt.mp; intro hlt
  have step1 : succ ℵ₀ ≤ γ.card := Order.succ_le_of_lt hlt
  have step2 : aleph 1 ≤ succ ℵ₀ := by rw [succ_aleph0]
  exact absurd ((step2.trans step1).trans_lt h) (lt_irrefl _)

/-- The ToType of any ordinal below ω₁ is countable. -/
private lemma countable_toType_of_lt_omega1 {γ : Ordinal} (hγ : γ < (aleph 1).ord) :
    Countable γ.ToType := by
  rw [← mk_le_aleph0_iff, mk_toType]
  exact card_le_aleph0_of_lt_omega1 hγ

/-- The set of ordinals strictly below any γ < ω₁ is countable. -/
private lemma countable_Iio_of_lt_omega1 {γ : Ordinal} (hγ : γ < (aleph 1).ord) :
    Countable (Set.Iio γ) := by
  haveI := countable_toType_of_lt_omega1 hγ
  exact Countable.of_equiv _ ToType.mk.toEquiv.symm

/-- Initial segments of ω₁ (as sets of `Omega1` elements) are countable.
This is the subtype-order version of `countable_Iio_of_lt_omega1`. -/
private lemma countable_Iio_omega1 (γ : Omega1) : (Set.Iio γ : Set Omega1).Countable := by
  -- The injection a ↦ ⟨a.1.val, a.2⟩ sends ↑(Iio γ : Set Omega1) into ↑(Iio γ.val : Set Ord)
  -- and the codomain is countable by countable_Iio_of_lt_omega1.
  haveI hcount := countable_Iio_of_lt_omega1 γ.2
  -- Goal: (Set.Iio γ : Set Omega1).Countable = Set.Countable (Set.Iio γ)
  -- = Countable ↥(Set.Iio γ : Set Omega1) (by definition of Set.Countable)
  show Countable ↑(Set.Iio γ : Set Omega1)
  -- Use Function.Injective.countable with the injection a ↦ ⟨a.1.val, a.2⟩.
  apply Function.Injective.countable (β := ↑(Set.Iio γ.val : Set Ordinal.{0}))
    (f := fun (a : ↑(Set.Iio γ : Set Omega1)) => (⟨a.1.val, a.2⟩ : ↑(Set.Iio γ.val)))
  intro ⟨⟨av, hav_ω₁⟩, hav_γ⟩ ⟨⟨bv, hbv_ω₁⟩, hbv_γ⟩ h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (Subtype.ext h)

/-- Any countable subset of ω₁ is bounded strictly below some element of ω₁.
This uses the key property that ω₁ has uncountable cofinality (it is regular). -/
private lemma countable_subset_bdd (S : Set Omega1) (hS : S.Countable) :
    ∃ γ : Omega1, ∀ s ∈ S, s < γ := by
  by_cases hemp : S.Nonempty
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hemp
    have hf_lt : ∀ n, (f n).1 < (aleph 1).ord := fun n => (f n).2
    have hbdd : BddAbove (Set.range (fun n => (f n).1)) :=
      ⟨(aleph 1).ord, fun o ⟨m, hm⟩ => hm ▸ (f m).2.le⟩
    -- The supremum of a countable sequence of ordinals below ω₁ is still below ω₁
    -- (by iSup_sequence_lt_omega_one, using that ω₁ has uncountable cofinality)
    have hlt : ⨆ n, (f n).1 < (aleph 1).ord :=
      iSup_sequence_lt_omega_one _ hf_lt
    have hsucc_lt : (⨆ n, (f n).1) + 1 < (aleph 1).ord := by
      rw [← succ_eq_add_one]
      exact (isSuccLimit_ord (aleph0_le_aleph 1)).succ_lt hlt
    refine ⟨⟨(⨆ n, (f n).1) + 1, hsucc_lt⟩, ?_⟩
    intro s hs; rw [hf] at hs; obtain ⟨n, rfl⟩ := hs
    show (f n).1 < (⨆ n, (f n).1) + 1
    rw [← succ_eq_add_one]
    exact lt_succ_of_le (le_ciSup hbdd n)
  · rw [Set.not_nonempty_iff_eq_empty] at hemp; rw [hemp]
    exact ⟨⟨0, isRegular_aleph_one.ord_pos⟩, fun s hs => absurd hs (Set.notMem_empty _)⟩

/--
**Prikry–Mills counterexample** (key lemma):

There exists a 2-colouring $f$ of a set of cardinality $\aleph_1$ cubed such that
no countable box $A_1 \times B_1 \times C_1$ is monochromatic.

This is the unpublished result of Prikry and Mills (1978). The proof proceeds by
transfinite induction along $\omega_1$, which has uncountable cofinality, ensuring
every countable box is non-monochromatic.
-/
@[category research solved, AMS 3 5]
theorem erdos_1128.prikryMills :
    ∃ (X : Type) (_ : #X = aleph 1) (f : X → X → X → Fin 2),
      ∀ (A₁ B₁ C₁ : Set X),
        #A₁ = aleph 0 → #B₁ = aleph 0 → #C₁ = aleph 0 →
        ¬ IsMonochromaticBox f A₁ B₁ C₁ := by
  -- The Prikry–Mills construction (1978, unpublished):
  -- Take X = (aleph 1).ord.ToType, which has cardinality ℵ₁ (by mk_ord_toType).
  --
  -- Construction by transfinite induction on γ < ω₁:
  -- * For each γ, since Iio γ is countable (card_le_aleph0_of_lt_omega1), choose an
  --   injection e_γ : Iio γ → ℕ. The injection is chosen to "kill" all countable
  --   boxes (A_ξ × B_ξ × C_ξ)_{ξ<γ} that are relevant to stage γ.
  -- * Define f(α, β, γ) = 0 if e_γ(α) < e_γ(β) when both α, β ∈ Iio γ; else f = 1.
  --   (Extend arbitrarily when the coordinates don't satisfy α, β < γ.)
  --
  -- Non-monochromaticity proof sketch:
  -- Given a putative monochromatic box A₁ × B₁ × C₁ (say with color 0), the
  -- diagonalization at the stage γ* = min(C₁ above sup(A₁ ∪ B₁)) ensures that
  -- e_{γ*} was specifically chosen so that the coloring is NOT constant on A₁ × B₁
  -- via γ*. The key counting argument:
  -- * sup(A₁ ∪ B₁) < ω₁ (by countable_subset_bdd, since A₁ ∪ B₁ is countable).
  -- * At stage γ*, the image e_{γ*}(A₁) ⊆ ℕ and e_{γ*}(B₁) ⊆ ℕ are both
  --   infinite, so neither "∀ a < all b" nor "∀ a > all b" can hold.
  -- * This gives a witness pair (α, β) where f(α, β, γ*) ≠ color 0.
  --
  -- The full formalization requires transfinite inductive choice (choosing e_γ for
  -- each γ via Well.rec or Ordinal.limitRecOn) and a careful stage counting argument
  -- using ω₁'s uncountable cofinality.
  sorry

/--
**Erdős Problem 1128** (disproved by Prikry–Mills, 1978):

Erdős asked whether every 2-colouring of $A \times B \times C$, where
$|A| = |B| = |C| = \aleph_1$, must contain a monochromatic countable box
$A_1 \times B_1 \times C_1$ with $|A_1| = |B_1| = |C_1| = \aleph_0$.

The answer is **No**: Prikry and Mills constructed a 2-colouring of $\omega_1^3$
with no monochromatic countable box.

Note: The positive statement asserts that every 2-colouring of every $\aleph_1^3$
contains a monochromatic countably infinite box. Since the answer is False, this
positive statement fails.
-/
@[category research solved, AMS 3 5]
theorem erdos_1128 : answer(False) ↔
    ∀ (A B C : Type) (_ : #A = aleph 1) (_ : #B = aleph 1) (_ : #C = aleph 1)
      (f : A → B → C → Fin 2),
      ∃ (A₁ : Set A) (B₁ : Set B) (C₁ : Set C),
        #A₁ = aleph 0 ∧ #B₁ = aleph 0 ∧ #C₁ = aleph 0 ∧
        IsMonochromaticBox f A₁ B₁ C₁ := by
  -- `answer(False)` reduces to `False` in the default elaborator mode.
  -- The goal is: False ↔ ∀ A B C, |A| = ℵ₁ → |B| = ℵ₁ → |C| = ℵ₁ →
  --               ∀ f, ∃ monochromatic countable box.
  -- (→): False implies anything.
  -- (←): The Prikry–Mills theorem provides A B C of size ℵ₁ and a 2-colouring
  --      with no monochromatic countable box, contradicting the hypothesis.
  constructor
  · intro h; exact h.elim
  · intro h
    -- Obtain the Prikry–Mills counterexample: a type X of cardinality ℵ₁ with a
    -- 2-colouring f : X → X → X → Fin 2 having no monochromatic countable box.
    obtain ⟨X, hX, f, hf⟩ := erdos_1128.prikryMills
    -- Apply h to X (playing the roles of A, B, C), using |X| = ℵ₁.
    obtain ⟨A₁, B₁, C₁, hA, hB, hC, hbox⟩ := h X X X hX hX hX f
    -- The Prikry–Mills theorem says no countably infinite box is monochromatic.
    -- Since #A₁ = aleph 0, #B₁ = aleph 0, #C₁ = aleph 0, this is a contradiction.
    exact hf A₁ B₁ C₁ hA hB hC hbox

/--
**Explicit form of Prikry–Mills**:

There exists a 2-colouring of $\omega_1 \times \omega_1 \times \omega_1$ such that
for every countably infinite $A_1, B_1, C_1 \subseteq \omega_1$, the box
$A_1 \times B_1 \times C_1$ is not monochromatic.

This is the content of the Prikry–Mills theorem (1978, unpublished), stated
using Lean's ordinal type `{o : Ordinal // o < (aleph 1).ord}` as the
representation of $\omega_1$.
-/
@[category research solved, AMS 3 5]
theorem erdos_1128.variants.prikryMills_explicit :
    ∃ (f : {o : Ordinal // o < (aleph 1).ord} →
           {o : Ordinal // o < (aleph 1).ord} →
           {o : Ordinal // o < (aleph 1).ord} → Fin 2),
      ∀ (A₁ B₁ C₁ : Set {o : Ordinal // o < (aleph 1).ord}),
        #A₁ = aleph 0 → #B₁ = aleph 0 → #C₁ = aleph 0 →
        ¬ IsMonochromaticBox f A₁ B₁ C₁ := by
  -- This is the explicit form of the Prikry–Mills theorem on
  -- ω₁ = {o : Ordinal // o < (aleph 1).ord}.
  --
  -- Key ingredients (all proved in the auxiliary lemmas above):
  -- 1. countable_Iio_of_lt_omega1: For each γ < ω₁, the set Iio γ is countable.
  -- 2. countable_subset_bdd: Any countable A₁ ⊆ ω₁ is bounded below ω₁.
  --    (Uses iSup_sequence_lt_omega_one and the regularity of ω₁.)
  --
  -- Construction: By transfinite induction, choose injections e_γ : Iio γ → ℕ
  -- (possible by countable_Iio_of_lt_omega1 and Countable.exists_injective_nat)
  -- to "kill" every countable box. The coloring is:
  --   f(α, β, γ) = 0 if e_γ(α) < e_γ(β)  (when α, β < γ)
  --   f(α, β, γ) = 1 otherwise
  --
  -- Non-monochromaticity: For any countable A₁, B₁, C₁ ⊆ ω₁, by
  -- countable_subset_bdd there exists γ ∈ C₁ above sup(A₁ ∪ B₁). At this γ,
  -- e_γ embeds A₁ ∪ B₁ injectively into ℕ, giving infinite disjoint images.
  -- Two infinite subsets of ℕ cannot have all elements of one strictly less than
  -- all elements of the other, giving a contradiction with monochromaticity.
  --
  -- Universe note: {o : Ordinal // o < (aleph 1).ord} lives in Type 1 while the
  -- abstract prikryMills uses X : Type 0. The construction here is self-contained
  -- and does not need to be reduced to prikryMills.
  sorry

/--
The claim that every 2-colouring of $\omega_1 \times \omega_1$ has an uncountable
monochromatic product rectangle is **false** in ZFC.

**Counterexample:** The ordering colouring $f(\alpha, \beta) = 0$ iff $\alpha < \beta$
has no uncountable monochromatic product rectangle $A_1 \times B_1$.

**Proof:** If $A_1 \times B_1$ were monochromatic with colour 0, then every element of
$A_1$ would be strictly less than every element of $B_1$, making $A_1$ bounded above in
$\omega_1$; but any bounded subset of $\omega_1$ is countable (since initial segments are
countable), contradicting $A_1$ being uncountable. The colour-1 case is symmetric with
the roles of $A_1$ and $B_1$ swapped.

Note: The correct classical result for 2-colourings of pairs (not products) is the
Erdős–Rado theorem $\omega_1 \to (\omega_1)^2_2$, which concerns unordered pairs.
-/
@[category research solved, AMS 3 5]
theorem erdos_1128.variants.two_dimensional_false :
    ¬ ∀ (f : Omega1 → Omega1 → Fin 2),
        ∃ (A₁ B₁ : Set Omega1),
          ¬ A₁.Countable ∧ ¬ B₁.Countable ∧
          ∃ c : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, f a b = c := by
  -- The ordering colouring f(α, β) = [α < β] is the counterexample.
  -- Introduce the negation: assume every colouring has an uncountable monochromatic rectangle.
  intro h
  -- Instantiate h with the ordering colouring f(α, β) = if α < β then 0 else 1.
  specialize h (fun a b => if a.val < b.val then 0 else 1)
  obtain ⟨A₁, B₁, hA_unc, hB_unc, c, hcol⟩ := h
  -- Key tool: bounded subsets of ω₁ (Omega1) are countable.
  -- Proof: if A₁ ⊆ Iio γ for some γ : Omega1, then A₁ ⊆ Iio γ and Iio γ is countable.
  -- Contrapositive: uncountable subsets of ω₁ are not bounded (i.e., cofinal in ω₁).
  have A₁_unbdd : ∀ γ : Omega1, ∃ a ∈ A₁, γ ≤ a := by
    intro γ
    by_contra hbdd
    push_neg at hbdd
    exact hA_unc (Set.Countable.mono (fun a ha => hbdd a ha) (countable_Iio_omega1 γ))
  have B₁_unbdd : ∀ γ : Omega1, ∃ b ∈ B₁, γ ≤ b := by
    intro γ
    by_contra hbdd
    push_neg at hbdd
    exact hB_unc (Set.Countable.mono (fun b hb => hbdd b hb) (countable_Iio_omega1 γ))
  -- A₁ and B₁ are both nonempty (since uncountable sets are nonempty).
  have hA_ne : A₁.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    exact hA_unc (hemp ▸ Set.countable_empty)
  have hB_ne : B₁.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    exact hB_unc (hemp ▸ Set.countable_empty)
  -- Case analysis on the colour c.
  fin_cases c
  · -- c = 0: ∀ a ∈ A₁, ∀ b ∈ B₁, a.val < b.val (since f a b = 0 iff a.val < b.val)
    -- A₁ is unbounded, so pick a ∈ A₁ with a ≥ b₀ for some b₀ ∈ B₁.
    obtain ⟨b₀, hb₀⟩ := hB_ne
    obtain ⟨a, haA, hba⟩ := A₁_unbdd b₀
    -- hcol a haA b₀ hb₀ says f a b₀ = 0, i.e., a.val < b₀.val.
    have hcol_val : a.val < b₀.val := by
      have h0 := hcol a haA b₀ hb₀
      simp only [Fin.isValue] at h0
      split_ifs at h0 with hlt
      · exact hlt
      · exact absurd h0 (by decide)
    -- But hba : b₀ ≤ a (as Omega1 elements), so b₀.val ≤ a.val. Contradiction.
    exact absurd hcol_val (not_lt.mpr (Subtype.mk_le_mk.mp hba))
  · -- c = 1: ∀ a ∈ A₁, ∀ b ∈ B₁, f a b = 1, i.e., ¬(a.val < b.val).
    -- B₁ is unbounded. Use B₁_unbdd with the successor of some a₀ ∈ A₁.
    obtain ⟨a₀, ha₀⟩ := hA_ne
    -- The successor a₀.val + 1 is still below ω₁ (since ω₁ is a limit ordinal).
    have ha₀_succ_lt : a₀.val + 1 < (aleph 1).ord := by
      rw [← succ_eq_add_one]
      exact (isSuccLimit_ord (aleph0_le_aleph 1)).succ_lt a₀.2
    obtain ⟨b', hb'B, hb'_ge⟩ := B₁_unbdd ⟨a₀.val + 1, ha₀_succ_lt⟩
    -- hb'_ge : ⟨a₀.val + 1, _⟩ ≤ b', so a₀.val + 1 ≤ b'.val, so a₀.val < b'.val.
    have hlt : a₀.val < b'.val := by
      have hle := Subtype.mk_le_mk.mp hb'_ge
      -- a₀.val < a₀.val + 1 ≤ b'.val
      have h_lt_succ : a₀.val < a₀.val + 1 := by
        rw [← succ_eq_add_one]; exact lt_succ a₀.val
      exact lt_of_lt_of_le h_lt_succ hle
    -- But hcol a₀ ha₀ b' hb'B = 1 means f a₀ b' = 1, i.e., ¬(a₀.val < b'.val).
    have hcol_val : ¬ (a₀.val < b'.val) := by
      have h1 := hcol a₀ ha₀ b' hb'B
      -- h1 : (if a₀.val < b'.val then 0 else 1) = 1
      simp only [Fin.isValue] at h1
      by_contra h_lt
      simp only [h_lt, ↓reduceIte] at h1
      exact absurd h1 (by decide)
    exact absurd hlt hcol_val

end Erdos1128
