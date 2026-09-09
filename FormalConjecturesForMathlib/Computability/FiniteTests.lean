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

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Range

/-!
# Finite tests and counterexample coverage

An exhaustive finite enumeration by size connects finite testing of candidates to universal
correctness. Every candidate fails some test if and only if every finite candidate prefix can
be refuted within one finite test bound. All enumeration and checking functions are explicit.

These are generic finite-set results. The intended application to clocked algorithms is motivated
by Oliveira, *Meta-Mathematics of Computational Complexity Theory*, ECCC TR25-041,
§5.1.2, https://eccc.weizmann.ac.il/report/2025/041/. That source's arithmetic theories and
SAT-search statement require additional syntax, computation, and representation theorems.
-/

@[expose] public section

namespace Computability.FiniteTests

variable {α β : Type*}

/-- An exhaustive finite enumeration with an explicit size measure. -/
structure Enumeration (α : Type*) where
  size : α → ℕ
  upTo : ℕ → Finset α
  mem_upTo : ∀ {a n}, a ∈ upTo n ↔ size a ≤ n

namespace Enumeration

theorem monotone (e : Enumeration α) : Monotone e.upTo :=
  fun _ _ h _ ha ↦ e.mem_upTo.mpr ((e.mem_upTo.mp ha).trans h)

theorem covers (e : Enumeration α) (a : α) : a ∈ e.upTo (e.size a) :=
  e.mem_upTo.mpr le_rfl

/-- Natural numbers enumerated by their value, for generic examples (not binary code length). -/
def naturals : Enumeration ℕ where
  size := id
  upTo n := Finset.range (n + 1)
  mem_upTo := by simp [Nat.lt_succ_iff]

/-- All bitstrings of length at most the bound, including the empty string. -/
def bitstringsUpTo : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => {[]} ∪ (bitstringsUpTo n).image (false :: ·) ∪
      (bitstringsUpTo n).image (true :: ·)

@[simp]
theorem mem_bitstringsUpTo {x : List Bool} {n : ℕ} :
    x ∈ bitstringsUpTo n ↔ x.length ≤ n := by
  induction n generalizing x with
  | zero => simp [bitstringsUpTo]
  | succ n ih =>
    cases x with
    | nil => simp [bitstringsUpTo]
    | cons b x => cases b <;> simp [bitstringsUpTo, ih, Nat.succ_le_succ_iff]

/-- The executable enumeration of bitstrings by their actual length. -/
def bitstrings : Enumeration (List Bool) where
  size := List.length
  upTo := bitstringsUpTo
  mem_upTo := mem_bitstringsUpTo

end Enumeration

/-- One candidate passes every test. -/
def Correct (check : α → β → Bool) (a : α) : Prop := ∀ x, check a x = true

/-- Every candidate has a failing test. -/
def Separation (check : α → β → Bool) : Prop := ∀ a, ∃ x, check a x = false

/-- A candidate passes all tests in the exhaustive prefix. -/
def Survives (inputs : Enumeration β) (check : α → β → Bool) (a : α) (n : ℕ) : Prop :=
  ∀ x ∈ inputs.upTo n, check a x = true

instance (inputs : Enumeration β) (check : α → β → Bool) (a : α) (n : ℕ) :
    Decidable (Survives inputs check a n) := by
  unfold Survives
  infer_instance

/-- Executable finite survival check. -/
def survives (inputs : Enumeration β) (check : α → β → Bool) (a : α) (n : ℕ) : Bool :=
  decide (Survives inputs check a n)

@[simp]
theorem survives_eq_true (inputs : Enumeration β) (check : α → β → Bool) (a : α) (n : ℕ) :
    survives inputs check a n = true ↔ Survives inputs check a n := by
  simp [survives]

theorem survives_iff (inputs : Enumeration β) (check : α → β → Bool) (a : α) (n : ℕ) :
    Survives inputs check a n ↔ ∀ x, inputs.size x ≤ n → check a x = true := by
  simp only [Survives, inputs.mem_upTo]

theorem Survives.mono {inputs : Enumeration β} {check : α → β → Bool} {a : α} {m n : ℕ}
    (h : Survives inputs check a n) (hmn : m ≤ n) : Survives inputs check a m :=
  fun x hx ↦ h x (inputs.monotone hmn hx)

theorem correct_iff_survives (inputs : Enumeration β) (check : α → β → Bool) (a : α) :
    Correct check a ↔ ∀ n, Survives inputs check a n :=
  ⟨fun h _ x _ ↦ h x, fun h x ↦ h (inputs.size x) x (inputs.covers x)⟩

theorem exists_correct_iff (inputs : Enumeration β) (check : α → β → Bool) :
    (∃ a, Correct check a) ↔ ∃ a, ∀ n, Survives inputs check a n :=
  exists_congr (correct_iff_survives inputs check)

theorem separation_iff_not_exists_correct (check : α → β → Bool) :
    Separation check ↔ ¬ ∃ a, Correct check a := by
  simp [Separation, Correct]

/-- Every enumerated candidate has a failing input within the given input bound. -/
def Excludes (candidates : Enumeration α) (inputs : Enumeration β)
    (check : α → β → Bool) (s n : ℕ) : Prop :=
  ∀ a ∈ candidates.upTo s, ∃ x ∈ inputs.upTo n, check a x = false

instance (candidates : Enumeration α) (inputs : Enumeration β)
    (check : α → β → Bool) (s n : ℕ) : Decidable (Excludes candidates inputs check s n) := by
  unfold Excludes
  infer_instance

/-- Executable exhaustive coverage check. -/
def excludes (candidates : Enumeration α) (inputs : Enumeration β)
    (check : α → β → Bool) (s n : ℕ) : Bool :=
  decide (Excludes candidates inputs check s n)

@[simp]
theorem excludes_eq_true (candidates : Enumeration α) (inputs : Enumeration β)
    (check : α → β → Bool) (s n : ℕ) :
    excludes candidates inputs check s n = true ↔ Excludes candidates inputs check s n := by
  simp [excludes]

theorem Excludes.mono_input {candidates : Enumeration α} {inputs : Enumeration β}
    {check : α → β → Bool} {s m n : ℕ} (h : Excludes candidates inputs check s m)
    (hmn : m ≤ n) : Excludes candidates inputs check s n := by
  intro a ha
  obtain ⟨x, hx, hf⟩ := h a ha
  exact ⟨x, inputs.monotone hmn hx, hf⟩

theorem Excludes.mono_candidate {candidates : Enumeration α} {inputs : Enumeration β}
    {check : α → β → Bool} {s t n : ℕ} (h : Excludes candidates inputs check t n)
    (hst : s ≤ t) : Excludes candidates inputs check s n :=
  fun a ha ↦ h a (candidates.monotone hst ha)

theorem excludes_of_empty {candidates : Enumeration α} (inputs : Enumeration β)
    (check : α → β → Bool) {s : ℕ} (h : candidates.upTo s = ∅) (n : ℕ) :
    Excludes candidates inputs check s n := by
  simp [Excludes, h]

/-- Finite counterexamples can be bounded uniformly over any finite candidate prefix. -/
theorem separation_iff_excludes (candidates : Enumeration α) (inputs : Enumeration β)
    (check : α → β → Bool) :
    Separation check ↔ ∀ s, ∃ n, Excludes candidates inputs check s n := by
  classical
  constructor
  · intro h s
    choose witness hw using h
    refine ⟨(candidates.upTo s).sup (fun a ↦ inputs.size (witness a)), ?_⟩
    intro a ha
    exact ⟨witness a,
      inputs.mem_upTo.mpr (Finset.le_sup (f := fun a ↦ inputs.size (witness a)) ha), hw a⟩
  · intro h a
    obtain ⟨n, hn⟩ := h (candidates.size a)
    obtain ⟨x, _, hx⟩ := hn a (candidates.covers a)
    exact ⟨x, hx⟩

end Computability.FiniteTests
