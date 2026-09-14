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

public import Mathlib.Computability.DFA

@[expose] public section

/-!
# Synchronizing words for DFAs

A **synchronizing word** (or reset word) for a DFA `M = (Q, Σ, δ)` is a word `w ∈ Σ*` such that
reading `w` from any state always leads to the same single state. A DFA is **synchronizing** if it
admits at least one synchronizing word.

These notions support the Černý conjecture (see `FormalConjectures.Wikipedia.CernyConjecture`).
-/

namespace DFA

variable {α : Type*} {σ : Type*}

/-- A word `w` is a **synchronizing word** (or reset word) for a DFA `M` if reading `w` from
any state leads to the same single state. -/
def IsSynchronizingWord (M : DFA α σ) (w : List α) : Prop :=
  ∃ p : σ, ∀ q : σ, M.evalFrom q w = p

/-- A DFA `M` is **synchronizing** if it has at least one synchronizing word. -/
def IsSynchronizing (M : DFA α σ) : Prop :=
  ∃ w : List α, M.IsSynchronizingWord w

/-- The empty word is a synchronizing word for `M` exactly when all states of `M` collapse to a
single one (equivalently, `σ` is a nonempty subsingleton). -/
@[simp]
theorem isSynchronizingWord_nil (M : DFA α σ) :
    M.IsSynchronizingWord [] ↔ ∃ p : σ, ∀ q : σ, q = p := by
  simp only [IsSynchronizingWord, evalFrom_nil]

/-- Appending any word `v` to a synchronizing word `w` yields a synchronizing word: reading `w`
already drives every state to a single state `p`, and reading `v` afterwards sends `p` to
`M.evalFrom p v` regardless of the starting state. -/
theorem IsSynchronizingWord.append {M : DFA α σ} {w : List α}
    (hw : M.IsSynchronizingWord w) (v : List α) : M.IsSynchronizingWord (w ++ v) := by
  obtain ⟨p, hp⟩ := hw
  refine ⟨M.evalFrom p v, fun q => ?_⟩
  rw [M.evalFrom_of_append, hp q]

/-- A DFA whose state type is a nonempty subsingleton (i.e. a single-state DFA) is trivially
synchronizing: the empty word already synchronizes it. -/
theorem isSynchronizing_of_subsingleton [Nonempty σ] [Subsingleton σ] (M : DFA α σ) :
    M.IsSynchronizing := by
  obtain ⟨p⟩ := ‹Nonempty σ›
  exact ⟨[], (isSynchronizingWord_nil M).2 ⟨p, fun q => Subsingleton.elim q p⟩⟩

end DFA
