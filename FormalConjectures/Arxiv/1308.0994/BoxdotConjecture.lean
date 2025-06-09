/-
Copyright 2025 The Formal Conjectures Authors.

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
# Boxdot Conjecture

This file defines the syntax and proof systems for modal logic, along with the
Boxdot translation and the Boxdot Conjecture. We introduce:

  * `Formula`: the inductive type for propositional modal formulas.
  * `t`: the recursive Boxdot translation function.
  * `KProof` and `KTProof`: axiomatizations of the basic K system and K plus T.
  * `NormalModalLogic`: a structure capturing any normal modal logic.
  * `KT`: the specific normal modal logic corresponding to K plus T.
  * `BoxdotConjecture`: states that if a logic agrees with KT on all
    boxdot-translations, then it cannot be strictly larger than KT.

The Boxdot Conjecture was originally formulated by French and Humberstone and
has been studied in several works. In particular, see:

*References:*
  - *Cluster Expansion and the Boxdot Conjecture*, Emil Jeřábek, arXiv:1308.0994.
  - *The Boxdot Conjecture and the Generalized McKinsey Axiom*, Christopher Steinsvold,
    Australasian Journal of Logic (AJL).
-/

namespace Boxdot

/--
`Formula` is the inductive type of propositional modal formulas:

* `Atom n` is a propositional variable indexed by `n`.
* `Falsum` is the constant ⊥.
* `Imp α β` is implication `(α → β)`.
* `Conj α β` is conjunction `(α ∧ β)`.
* `Nec α` is the necessity operator `□α`.
-/
inductive Formula : Type
  /-- `Atom n` is a propositional variable indexed by `n`. -/ 
  | Atom : Nat → Formula
  /--  `Falsum` is the constant ⊥. -/
  | Falsum : Formula
  /-- `Imp α β` is implication `(α → β)`. -/
  | Imp : Formula → Formula → Formula
  /-- `Conj α β` is conjunction `(α ∧ β)`. -/
  | Conj : Formula → Formula → Formula
  /-- `Nec α` is the necessity operator `□α`. -/
  | Nec : Formula → Formula

open Formula

local notation "⊥" => Falsum
infixr:80 " ~> " => Formula.Imp
infixr:85 " & " => Formula.Conj
notation:max " ~ " φ => φ ~> ⊥
prefix:95 "□" => Nec


/--
`t φ` is the Boxdot translation of a formula `φ`.
This implementation follows the definition in Steinsvold (AJL).
-/
def t (φ : Formula) : Formula :=
  match φ with
  | α ~> β => t α ~> t β
  | □α => □t α & t α
  | _ => φ

prefix:95 "■" => t


/--
`KProof Γ φ` is the usual Hilbert‐style proof relation for the minimal normal modal logic K,
with assumptions drawn from `Γ`.
-/
inductive KProof : Set Formula → Formula → Prop
| ax {Γ} {α} (h : α ∈ Γ) : KProof Γ α
| ax1 {Γ} {α β} : KProof Γ (α ~> β ~> α)
| ax2 {Γ} {α β γ} : KProof Γ ((α ~> β ~> γ) ~> (α ~> β) ~> (α ~> γ))
| ax3 {Γ} {α β} : KProof Γ (((~α) ~> (~β)) ~> (β ~> α))
| mp {Γ} {α β} (_ : KProof Γ (α ~> β)) (_ : KProof Γ α) : KProof Γ β
| nec {Γ} {α} (_ : KProof ∅ α) : KProof Γ (□ α)
| distr {Γ} {α β} : KProof Γ (□ (α ~> β) ~> □ α ~> □ β)


-- This is an axiomatization of the modal logic KT, which extends K with the T axiom
inductive KTProof : Set Formula → Formula → Prop
| lift_K {Γ} {α} (h : KProof Γ α) : KTProof Γ α
| axT {Γ} {α} : KTProof Γ (□ α ~> α)
| mp {Γ} {α β} (_ : KTProof Γ (α ~> β)) (_ : KTProof Γ α) : KTProof Γ β
| nec {Γ} {α} (_ : KTProof ∅ α) : KTProof Γ (□ α)


open KProof
open KTProof


/--
If `KProof Γ φ`, then `KTProof Γ φ`.  In other words, KT extends K.
-/
@[category API, AMS 3]
lemma KTExtendsK {Γ φ} (h : KProof Γ φ) : KTProof Γ φ :=
  lift_K h

/--
  A “normal modal logic” L is any `Set Formula` such that:
    1. If K ⊢ φ, then φ ∈ L            (L extends K)
    2. If φ ∈ L and (φ → ψ) ∈ L, then ψ ∈ L  (Closed under MP)
    3. If φ ∈ L, then □φ ∈ L           (Closed under Necessitation)
-/
structure NormalModalLogic : Type where
  thms : Set Formula
  extK : ∀ {φ}, KProof ∅ φ → φ ∈ thms
  mp : ∀ {φ ψ}, φ ∈ thms → (φ ~> ψ) ∈ thms → ψ ∈ thms
  nec : ∀ {φ}, φ ∈ thms → □ φ ∈ thms


def proves (L : NormalModalLogic) (φ : Formula) := φ ∈ L.thms


infixr:85 " ⊢ " => proves
notation L " ⊆ " L' =>
  NormalModalLogic.thms L ⊆ NormalModalLogic.thms L'


/--
`KT` is the specific normal modal logic whose theorems are exactly those provable
in `KTProof` from the empty context.

This corresponds to K ⊕ (□φ → φ) as in both AJL (Steinsvold) and Jeřábek.
-/
def KT : NormalModalLogic := by
  constructor
  case thms =>
    exact {φ | KTProof ∅ φ}
  case extK =>
    intro _ h
    exact KTExtendsK h
  case mp =>
    intro φ ψ h₁ h₂
    simp [Set.mem_setOf_eq] at *
    exact KTProof.mp h₂ h₁
  case nec =>
    intro φ h
    simp [Set.mem_setOf_eq] at *
    exact KTProof.nec h


/--
  Boxdot Conjecture: every normal modal logic that faithfully interprets KT
  by the boxdot translation is included in KT.
-/
@[category research solved, AMS 3]
theorem BoxdotConjecture (L : NormalModalLogic) :
    (∀ φ, L ⊢ ■ φ ↔ KT ⊢ φ) → L ⊆ KT := by
  sorry


end Boxdot
