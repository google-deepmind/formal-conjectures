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

import Mathlib

/-!
# Boxdot Conjecture

The Boxdot Conjecture was originally formulated by French and Humberstone and
has been studied in several works. In particular, see:

*References:*
- [arxiv/1308.0994](https://arxiv.org/abs/1308.0994)
  **Cluster Expansion and the Boxdot Conjecture** by *Emil Jeřábek*
- [The Boxdot Conjecture and the Generalized McKinsey Axiom](https://ojs.victoria.ac.nz/ajl/article/view/4891)
  by *Christopher Steinsvold*, Australasian Journal of Logic

-/

namespace Arxiv.«1308.0994»

/--
`Formula` is the inductive type of propositional modal formulas:

* `Atom n` is a propositional variable indexed by `n`.
* `Falsum` is the constant ⊥.
* `Imp α β` is implication `(α → β)`.
* `Nec α` is the necessity operator `□α`.
-/
inductive Formula : Type
  /-- `Atom n` is a propositional variable indexed by `n`. -/
  | Atom : Nat → Formula
  /--  `Falsum` is the constant ⊥. -/
  | Falsum : Formula
  /-- `Imp α β` is implication `(α → β)`. -/
  | Imp : Formula → Formula → Formula
  /-- `Nec α` is the necessity operator `□α`. -/
  | Nec : Formula → Formula

open Formula

@[inherit_doc Falsum]
scoped notation "⊥" => Falsum

@[inherit_doc Imp]
infixr:80 " ~> " => Formula.Imp

/-- `~ α` is the negation of `α`. `~ α` is also equivalent to `α ~> ⊥`. -/
scoped notation:max " ~ " φ => φ ~> ⊥

@[inherit_doc Nec]
scoped prefix:95 "□" => Nec

/-- `Conj α β` is the conjunction `α ∧ β`. We define `α & β` as `~(α ~> ~β)` for simplicity. -/
@[reducible]
def Conj (α β : Formula) : Formula := ~(α ~> ~β)

@[inherit_doc Conj]
scoped infixr:85 " & " => Conj

/--
`t φ` is the Boxdot translation of a formula `φ`. Roughly, t is the mapping `φ ↦ t φ`
from the language of monomodal logic into itself that preserves variables and the logical constant `⊥`,
commutes with the standard truth-functional operators, and is such that `t □a` = `□t a & t a`.
This implementation follows the definition in Steinsvold (AJL).
-/
def t (φ : Formula) : Formula :=
  match φ with
  | α ~> β => t α ~> t β
  | □α => □t α & t α
  | _ => φ

@[inherit_doc t]
scoped prefix:95 "■" => t


/--
`KProof Γ φ` is the usual Hilbert‐style proof relation for the minimal normal modal logic K,
with assumptions drawn from `Γ`.
-/
inductive KProof : Set Formula → Formula → Prop
/-- Assumption rule: if `α ∈ Γ` then `α` is provable from `Γ`. -/
| ax {Γ} {α} (h : α ∈ Γ) : KProof Γ α
/-- Ax1: every instance of the schema `α → (β → α)` is a theorem. -/
| ax1 {Γ} {α β} : KProof Γ (α ~> β ~> α)
/-- Ax2: every instance of the schema `(α ~> β ~> γ) ~> (α ~> β) ~> (α ~> γ)` is a theorem. -/
| ax2 {Γ} {α β γ} : KProof Γ ((α ~> β ~> γ) ~> (α ~> β) ~> (α ~> γ))
/-- Ax3 (contraposition): every instance of the schema `(~α ~> ~β) ~> (β ~> α)` is a theorem. -/
| ax3 {Γ} {α β} : KProof Γ (((~α) ~> (~β)) ~> (β ~> α))
/-- Modus Ponens: if `Γ ⊢ α ~> β` and `Γ ⊢ α`, then `Γ ⊢ β`. -/
| mp {Γ} {α β} (_ : KProof Γ (α ~> β)) (_ : KProof Γ α) : KProof Γ β
/-- Necessitation: if `⊢ α` then `⊢ □α`. -/
| nec {Γ} {α} (_ : KProof ∅ α) : KProof Γ (□ α)
/-- Distribution: every instance of the schema `□(α ~> β) ~> (□α ~> □β)` is a theorem. -/
| distr {Γ} {α β} : KProof Γ (□ (α ~> β) ~> □ α ~> □ β)


/--
`KTProof Γ φ` denotes that `φ` is provable from the premises `Γ` in the normal modal logic KT
(also called T). KT extends system K by adding the instances of the T-axiom schema `□φ ~> φ` to K’s
usual axioms and rules of inference.
-/
inductive KTProof : Set Formula → Formula → Prop
/-- Embedding of K proofs into KT. -/
| lift_K {Γ} {α} (h : KProof Γ α) : KTProof Γ α
/-- T-axiom schema: every instance of `□α ~> α` is a theorem. -/
| axT {Γ} {α} : KTProof Γ (□ α ~> α)
/-- Modus Ponens: if `Γ ⊢ α ~> β` and `Γ ⊢ α`, then `Γ ⊢ β`. -/
| mp {Γ} {α β} (_ : KTProof Γ (α ~> β)) (_ : KTProof Γ α) : KTProof Γ β
/-- Necessitation: if `⊢ α` then `⊢ □α`. -/
| nec {Γ} {α} (_ : KTProof ∅ α) : KTProof Γ (□ α)


open KProof KTProof


/--
If `KProof Γ φ`, then `KTProof Γ φ`. In other words, KT extends K.
-/
lemma KTExtendsK {Γ φ} (h : KProof Γ φ) : KTProof Γ φ :=
  lift_K h

/--
A “normal modal logic” L is any `Set Formula` such that:
  1. If `K ⊢ φ`, then `φ ∈ L`          (L extends K)
  2. If `φ ∈ L` and `(φ ~> ψ) ∈ L`, then `ψ ∈ L`  (Closed under MP)
  3. If `φ ∈ L`, then `□φ ∈ L`          (Closed under Necessitation)
-/
structure NormalModalLogic : Type where
  /-- `thms` is the set of formulas proveable in the logic. -/
  thms : Set Formula
  /-- `extK` means that if `K ⊢ φ`, then `φ ∈ thms`. That is, the logic extends system K. -/
  extK : ∀ {φ}, KProof ∅ φ → φ ∈ thms
  /-- `mp` means that if `φ ∈ thms` and `(φ ~> ψ) ∈ thms`, then `ψ ∈ thms`. That is, thms is closed
  under modus ponens. -/
  mp : ∀ {φ ψ}, φ ∈ thms → (φ ~> ψ) ∈ thms → ψ ∈ thms
  /-- `nec` means that if `φ ∈ thms`, then `□φ ∈ thms`. Equivalently, `thms` is closed under
  necessitation -/
  nec : ∀ {φ}, φ ∈ thms → □ φ ∈ thms


def proves (L : NormalModalLogic) (φ : Formula) := φ ∈ L.thms


scoped infixr:85 " ⊢ " => proves
scoped notation L " ⊆ " L' =>
  NormalModalLogic.thms L ⊆ NormalModalLogic.thms L'


/--
`KT` is the specific normal modal logic whose theorems are exactly those provable
in `KTProof` from the empty context.

This corresponds to `K ⊕ (□φ → φ)` as in both AJL (Steinsvold) and Jeřábek.
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
-- The formal proof was done by Mashu Noguchi et al.
-- see linked repo for the full list of contributors
theorem BoxdotConjecture (L : NormalModalLogic) (H : ∀ φ, L ⊢ ■ φ ↔ KT ⊢ φ) : L ⊆ KT := by
  sorry

end Arxiv.«1308.0994»
