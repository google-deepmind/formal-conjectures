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

public import FormalConjecturesForMathlib.Computability.Complexity

/-!
# Polynomial-time reductions and separators for promise problems

A promise problem has specified yes and no regions. Algorithms must be correct
on those regions; no answer is prescribed between them. NP-hardness uses
deterministic many-one reductions from every language in the existing NP class,
with actual TM2 polynomial-time witnesses. Disjointness is explicit, excluding
the degenerate claim that a constant reduction to an overlapping pair is hard.

Reference: Goldreich, *On Promise Problems*, July 2005 author version,
§1.2, Definitions 1.1–1.3 (published in 2006 as *On Promise Problems: A Survey*):
https://www.wisdom.weizmann.ac.il/~oded/PSX/prpr-r.pdf.
-/

@[expose] public section

namespace ComplexityTheory

/-- A total polynomial-time map preserving both promised regions. -/
def PromiseReduction {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (yes no : α → Prop) (yes' no' : β → Prop) : Prop :=
  ∃ f : α → β, IsPolyTime f ∧
    (∀ x, yes x → yes' (f x)) ∧ (∀ x, no x → no' (f x))

/-- A promise problem is NP-hard via actual deterministic polynomial-time reductions. -/
def PromiseNPHard {α : Type} [BitstringEncoding α] (yes no : α → Prop) : Prop :=
  (∀ x, yes x → ¬ no x) ∧ ∀ L : DecisionProblem, L ∈ NP →
    PromiseReduction (fun x => L x = true) (fun x => L x = false) yes no

/-- A total polynomial-time separator, unconstrained outside the two promised regions. -/
def HasPolyTimeSeparator {α : Type} [BitstringEncoding α] (yes no : α → Prop) : Prop :=
  ∃ f : α → Bool, IsPolyTime f ∧
    (∀ x, yes x → f x = true) ∧ (∀ x, no x → f x = false)

theorem PromiseReduction.refl {α : Type} [BitstringEncoding α] (yes no : α → Prop) :
    PromiseReduction yes no yes no :=
  ⟨id, isPolyTime_id, fun _ h => h, fun _ h => h⟩

/-- Weakening the target promises preserves hardness when they remain disjoint. -/
theorem PromiseNPHard.mono {α : Type} [BitstringEncoding α] {yes no yes' no' : α → Prop}
    (h : PromiseNPHard yes no)
    (hy : ∀ x, yes x → yes' x) (hn : ∀ x, no x → no' x)
    (hd : ∀ x, yes' x → ¬ no' x) : PromiseNPHard yes' no' := by
  refine ⟨hd, fun L hL => ?_⟩
  obtain ⟨f, hf, hfy, hfn⟩ := h.2 L hL
  exact ⟨f, hf, fun x hx => hy _ (hfy x hx), fun x hx => hn _ (hfn x hx)⟩

/-- A Boolean separator cannot accept and reject the same promised input. -/
theorem HasPolyTimeSeparator.disjoint {α : Type} [BitstringEncoding α] {yes no : α → Prop}
    (h : HasPolyTimeSeparator yes no) : ∀ x, yes x → ¬ no x := by
  obtain ⟨f, _, hy, hn⟩ := h
  intro x hx hx'
  have := hy x hx
  rw [hn x hx'] at this
  cases this

/-- An arbitrary input-dependent time bound for a deterministic promise separator.
The one finite TM2 machine is chosen before the input. -/
def HasTimeSeparator {α : Type} [BitstringEncoding α]
    (yes no : α → Prop) (time : α → ℕ) : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ x,
    (yes x → Nonempty (Turing.TM2OutputsInTime M.tm
      ((BitstringEncoding.bitEncode x).map M.inputAlphabet.invFun)
      (some ((BitstringEncoding.bitEncode true).map M.outputAlphabet.invFun)) (time x))) ∧
    (no x → Nonempty (Turing.TM2OutputsInTime M.tm
      ((BitstringEncoding.bitEncode x).map M.inputAlphabet.invFun)
      (some ((BitstringEncoding.bitEncode false).map M.outputAlphabet.invFun)) (time x)))

theorem HasTimeSeparator.mono {α : Type} [BitstringEncoding α]
    {yes no : α → Prop} {s t : α → ℕ} (h : HasTimeSeparator yes no s)
    (hst : ∀ x, s x ≤ t x) : HasTimeSeparator yes no t := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    obtain ⟨hRun⟩ := (hM x).1 hx
    exact ⟨⟨hRun.toEvalsTo, hRun.steps_le_m.trans (hst x)⟩⟩
  · intro hx
    obtain ⟨hRun⟩ := (hM x).2 hx
    exact ⟨⟨hRun.toEvalsTo, hRun.steps_le_m.trans (hst x)⟩⟩

end ComplexityTheory
