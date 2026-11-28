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
# Kourovka Notebook Problem 1.12 — Triviality of balanced presentations

W. Magnus asked whether one algorithm can recognize the trivial group among presentations
with $n$ generators and $n$ defining relations for $n > 2$. M. D. Greendlinger contributed the
problem to the first edition of the notebook.

The Adian–Rabin theorem gives undecidability for unrestricted finite presentations. The
Andrews–Curtis conjecture concerns the same balanced presentations of the trivial group. It
predicts that their relators can be transformed into the original generators by elementary
Andrews–Curtis moves. A search for such moves would give a certificate for a positive answer.

*References:*
- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300), Problem 1.12.
- [Formal Conjectures issue #1909](https://github.com/google-deepmind/formal-conjectures/issues/1909).
- M. O. Rabin, [Recursive unsolvability of group theoretic problems](https://doi.org/10.2307/1969933).
- M. Bridson, [The complexity of balanced presentations and the Andrews–Curtis conjecture](https://arxiv.org/abs/1504.04187).
-/

@[expose] public section

namespace Kourovka.«1.12»

/-- A finite presentation given by words in the generators and their inverses.
A positive letter has sign `true`. Relators may be repeated or empty. -/
structure FinitePresentation where
  numGens : ℕ
  rels : List (List (Fin numGens × Bool))

namespace FinitePresentation

/-- Store the generator count and erase the bounds on the generator indices. -/
def toCode (p : FinitePresentation) : ℕ × List (List (ℕ × Bool)) :=
  (p.numGens, p.rels.map (List.map fun a => (a.1.val, a.2)))

/-- Read a presentation code, dropping letters whose indices exceed the available range. -/
def ofCode (c : ℕ × List (List (ℕ × Bool))) : FinitePresentation :=
  ⟨c.1, c.2.map (List.filterMap fun a =>
    if h : a.1 < c.1 then some (⟨a.1, h⟩, a.2) else none)⟩

@[category API, AMS 3 20]
theorem ofCode_toCode (p : FinitePresentation) : ofCode p.toCode = p := by
  cases p
  simp [ofCode, toCode, List.map_map, Function.comp_def, List.filterMap_map]

/-- The code uses the standard encodings of natural numbers, pairs, booleans and lists.
Re-encoding a decoded input filters out-of-range letters, a primitive recursive operation. -/
instance : Primcodable FinitePresentation :=
  Primcodable.ofLeftInverse toCode ofCode ofCode_toCode (by
    have h : Primrec₂ fun (n : ℕ) (w : List (ℕ × Bool)) =>
        w.filterMap fun a => if a.1 < n then some a else none :=
      (Primrec.listFilterMap Primrec.snd (Primrec.ite
        (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.option_some_iff.mpr Primrec.snd) (Primrec.const none)).to₂).to₂
    refine (Primrec.pair Primrec.fst (Primrec.list_map Primrec.snd
      (h.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right))).of_eq ?_
    intro c
    simp only [toCode, ofCode, List.map_map, Function.comp_def, List.map_filterMap]
    congr 1
    apply List.map_congr_left
    intro w _
    congr 1
    funext a
    split <;> rfl)

/-- The relators as elements of the free group, indexed by their positions in the input. -/
def relatorSet (p : FinitePresentation) : Set (FreeGroup (Fin p.numGens)) :=
  Set.range fun i : Fin p.rels.length => FreeGroup.mk p.rels[i]

end FinitePresentation

/-- A presentation is balanced if it has as many relators as generators. -/
def IsBalanced (p : FinitePresentation) : Prop := p.rels.length = p.numGens

/-- The group defined by the presentation has just one element. -/
def IsTrivialPresentation (p : FinitePresentation) : Prop :=
  Subsingleton (PresentedGroup p.relatorSet)

/-- Is there an algorithm deciding triviality for balanced presentations on more than two
generators, uniformly in the number of generators? -/
@[category research open, question, AMS 3 20]
theorem kourovka_1_12 :
    ∃ f : FinitePresentation → Bool, Computable f ∧
      ∀ p, IsBalanced p → 2 < p.numGens → (f p = true ↔ IsTrivialPresentation p) := by
  sorry

/-- Does an algorithm decide triviality for balanced presentations on at least two generators?
A two-generator input can be padded with a third generator and a relator killing it. -/
@[category research open, question, AMS 3 20]
theorem kourovka_1_12.variants.two_le :
    ∃ f : FinitePresentation → Bool, Computable f ∧
      ∀ p, IsBalanced p → 2 ≤ p.numGens → (f p = true ↔ IsTrivialPresentation p) := by
  sorry

/-- The Adian–Rabin theorem implies that triviality of arbitrary finite presentations
is undecidable. -/
@[category research solved, AMS 3 20]
theorem kourovka_1_12.variants.general_undecidable : ¬ ComputablePred IsTrivialPresentation := by
  sorry

/-- A presented group is trivial exactly when each generator represents the identity. -/
@[category API, AMS 20]
theorem isTrivialPresentation_iff (p : FinitePresentation) :
    IsTrivialPresentation p ↔ ∀ i, PresentedGroup.of (rels := p.relatorSet) i = 1 := by
  constructor
  · exact fun h i => h.elim _ _
  · intro h
    have he (x : PresentedGroup p.relatorSet) : x = 1 :=
      PresentedGroup.generated_by _ ⊥ h x
    exact ⟨fun x y => (he x).trans (he y).symm⟩

/-- The exponent sum of a word on one generator counts positive letters minus negative letters. -/
def exponentSum (w : List (Fin 1 × Bool)) : ℤ :=
  (w.map fun a => bif a.2 then (1 : ℤ) else -1).sum

/-- A word on one generator is the generator raised to the exponent sum of the word. -/
@[category API, AMS 20]
theorem mk_eq_zpow_exponentSum (w : List (Fin 1 × Bool)) :
    FreeGroup.mk w = FreeGroup.of (0 : Fin 1) ^ exponentSum w := by
  have h := FreeGroup.equivIntOfUnique.left_inv (FreeGroup.mk w)
  change FreeGroup.of (0 : Fin 1) ^ _ = FreeGroup.mk w at h
  simpa [FreeGroup.equivIntOfUnique, FreeGroup.map.mk, FreeGroup.sum_mk,
    List.map_map, Function.comp_def, exponentSum] using h.symm

/-- A one-generator, one-relator presentation is trivial exactly when the absolute value
of the exponent sum of its relator is one. -/
@[category API, AMS 20]
theorem kourovka_1_12.variants.one_gen (w : List (Fin 1 × Bool)) :
    IsTrivialPresentation ⟨1, [w]⟩ ↔ (exponentSum w).natAbs = 1 := by
  let p : FinitePresentation := ⟨1, [w]⟩
  let k := exponentSum w
  let x := PresentedGroup.of (rels := p.relatorSet) (0 : Fin 1)
  have hr : FreeGroup.mk w ∈ p.relatorSet := ⟨0, rfl⟩
  constructor
  · intro ht
    let g := Multiplicative.ofAdd (1 : ZMod k.natAbs)
    have hg : g ^ k = 1 := pow_natAbs_eq_one.mp (by
      change k.natAbs • (1 : ZMod k.natAbs) = 0
      simp)
    have hrels : ∀ r ∈ p.relatorSet, FreeGroup.lift (fun _ => g) r = 1 := by
      rintro _ ⟨i, rfl⟩
      rw [Fin.eq_zero i]
      change FreeGroup.lift _ (FreeGroup.mk w) = 1
      rw [mk_eq_zpow_exponentSum, map_zpow, FreeGroup.lift_apply_of]
      exact hg
    have hx := congrArg (PresentedGroup.toGroup hrels) (show x = 1 from ht.elim _ _)
    have h1 : (1 : ZMod k.natAbs) = 0 := by simpa [x, g] using hx
    exact Nat.dvd_one.mp ((ZMod.natCast_eq_zero_iff 1 _).mp (by simpa using h1))
  · intro hk
    have hx : x ^ k = 1 := by
      simpa only [x, k, PresentedGroup.of, mk_eq_zpow_exponentSum, map_zpow] using
        PresentedGroup.one_of_mem hr
    have hx' := pow_natAbs_eq_one.mpr hx
    rw [show k.natAbs = 1 from hk, pow_one] at hx'
    apply (isTrivialPresentation_iff p).mpr
    intro i
    rw [Fin.eq_zero i]
    exact hx'

/-- The empty presentation defines the trivial group. -/
@[category test, AMS 20]
theorem empty_presentation :
    let p : FinitePresentation := ⟨0, []⟩
    IsBalanced p ∧ IsTrivialPresentation p :=
  ⟨rfl, (isTrivialPresentation_iff _).mpr fun i => Fin.elim0 i⟩

/-- Killing the unique generator gives the trivial group. -/
@[category test, AMS 20]
theorem one_generator_killed :
    let p : FinitePresentation := ⟨1, [[(0, true)]]⟩
    IsBalanced p ∧ IsTrivialPresentation p :=
  ⟨rfl, (kourovka_1_12.variants.one_gen _).mpr rfl⟩

/-- Killing the square of the unique generator leaves a nontrivial group. -/
@[category test, AMS 20]
theorem one_generator_squared :
    let p : FinitePresentation := ⟨1, [[(0, true), (0, true)]]⟩
    IsBalanced p ∧ ¬ IsTrivialPresentation p :=
  ⟨rfl, fun h => (by decide : (2 : ℕ) ≠ 1) ((kourovka_1_12.variants.one_gen _).mp h)⟩

/-- Killing each of three generators gives a trivial group in the range of Magnus's question. -/
@[category test, AMS 20]
theorem three_generators_killed :
    let p : FinitePresentation := ⟨3, [[(0, true)], [(1, true)], [(2, true)]]⟩
    IsBalanced p ∧ 2 < p.numGens ∧ IsTrivialPresentation p := by
  intro p
  refine ⟨rfl, by decide, (isTrivialPresentation_iff p).mpr fun i => ?_⟩
  apply PresentedGroup.one_of_mem
  exact ⟨i, by fin_cases i <;> rfl⟩

/-- Three empty relators leave the free group on three generators, which is nontrivial. -/
@[category test, AMS 20]
theorem three_empty_relators :
    let p : FinitePresentation := ⟨3, [[], [], []]⟩
    IsBalanced p ∧ 2 < p.numGens ∧ ¬ IsTrivialPresentation p := by
  intro p
  refine ⟨rfl, by decide, fun h => ?_⟩
  let g := Multiplicative.ofAdd (1 : ℤ)
  have hrels : ∀ r ∈ p.relatorSet, FreeGroup.lift (fun _ => g) r = 1 := by
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> rfl
  have he := congrArg (PresentedGroup.toGroup hrels) ((isTrivialPresentation_iff p).mp h 0)
  simp [g] at he

end Kourovka.«1.12»
