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

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.OfFn

/-!
# Finite words and common-string decision problems

Reference: Garey and Johnson, *Computers and Intractability* (1979),
SR8–SR10, p. 228. https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf

The alphabet is explicitly represented by its size; symbols are natural-number indices.
Subsequence means deletion of arbitrary positions (Mathlib's `List.Sublist`).
Substring means contiguous occurrence (Mathlib's `List.IsInfix`).
Word bounds give finite exhaustive decision procedures, not efficient algorithms.
-/

@[expose] public section

namespace Computability.StringProblems

/-- Every symbol lies in the specified finite alphabet. -/
def WordIn (m : ℕ) (w : List ℕ) : Prop := ∀ a ∈ w, a < m

instance (m : ℕ) (w : List ℕ) : Decidable (WordIn m w) :=
  inferInstanceAs (Decidable (∀ a ∈ w, a < m))

/-- Validate all strings without removing duplicates or empty strings. -/
def StringsIn (m : ℕ) (xs : List (List ℕ)) : Prop := ∀ w ∈ xs, WordIn m w

instance (m : ℕ) (xs : List (List ℕ)) : Decidable (StringsIn m xs) :=
  inferInstanceAs (Decidable (∀ w ∈ xs, WordIn m w))

/-- Interpret a valid indexed word over its finite alphabet. -/
def typedWord {m : ℕ} (w : List ℕ) (h : WordIn m w) : List (Fin m) :=
  w.attach.map fun a ↦ ⟨a.val, h a.val a.property⟩

/-- Forget only the alphabet-bound proofs, preserving order and multiplicity. -/
def wordValues {m : ℕ} (w : List (Fin m)) : List ℕ := w.map Fin.val

@[simp]
theorem wordValues_typedWord {m : ℕ} (w : List ℕ) (h : WordIn m w) :
    wordValues (typedWord w h) = w := by
  simp [wordValues, typedWord, List.map_map]

@[simp]
theorem length_wordValues {m : ℕ} (w : List (Fin m)) :
    (wordValues w).length = w.length := by simp [wordValues]

/-- Finite enumeration of words of length at most K, including the empty word. -/
def BoundedWord {α : Type} (K : ℕ) (p : List α → Prop) : Prop :=
  ∃ n : Fin (K + 1), ∃ letters : Fin n.val → α, p (List.ofFn letters)

instance {α : Type} [Fintype α] (K : ℕ) (p : List α → Prop) [DecidablePred p] :
    Decidable (BoundedWord K p) :=
  inferInstanceAs (Decidable (∃ n : Fin (K + 1), ∃ _ : Fin n.val → α, _))

theorem boundedWord_iff {α : Type} (K : ℕ) (p : List α → Prop) :
    BoundedWord K p ↔ ∃ w, w.length ≤ K ∧ p w := by
  constructor
  · rintro ⟨n, letters, hp⟩
    exact ⟨List.ofFn letters, by simpa using Nat.le_of_lt_succ n.isLt, hp⟩
  · rintro ⟨w, hlen, hp⟩
    exact ⟨⟨w.length, Nat.lt_succ_of_le hlen⟩, w.get, by simpa using hp⟩

/-- Alphabet size, list of strings, and length threshold. Both collection size and
threshold are part of the input. -/
abbrev CommonInput := ℕ × List (List ℕ) × ℕ

/-- SR8: a common supersequence of length at most the positive threshold. -/
def CommonSupersequence (x : CommonInput) : Prop :=
  StringsIn x.1 x.2.1 ∧ 0 < x.2.2 ∧ BoundedWord x.2.2
    (fun w : List (Fin x.1) ↦ ∀ s ∈ x.2.1, s.Sublist (wordValues w))

instance (x : CommonInput) : Decidable (CommonSupersequence x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- SR9: a common contiguous superstring of length at most the positive threshold. -/
def CommonSuperstring (x : CommonInput) : Prop :=
  StringsIn x.1 x.2.1 ∧ 0 < x.2.2 ∧ BoundedWord x.2.2
    (fun w : List (Fin x.1) ↦ ∀ s ∈ x.2.1, s.IsInfix (wordValues w))

instance (x : CommonInput) : Decidable (CommonSuperstring x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- SR10: a common subsequence of the positive threshold length.
Truncation makes this equivalent to the source's lower bound on length. -/
def CommonSubsequence (x : CommonInput) : Prop :=
  StringsIn x.1 x.2.1 ∧ 0 < x.2.2 ∧
    ∃ letters : Fin x.2.2 → Fin x.1,
      ∀ s ∈ x.2.1, (wordValues (List.ofFn letters)).Sublist s

instance (x : CommonInput) : Decidable (CommonSubsequence x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∃ _ : Fin x.2.2 → Fin x.1, _))

theorem commonSubsequence_iff (x : CommonInput) :
    CommonSubsequence x ↔ StringsIn x.1 x.2.1 ∧ 0 < x.2.2 ∧
      ∃ w : List (Fin x.1), x.2.2 ≤ w.length ∧ ∀ s ∈ x.2.1, (wordValues w).Sublist s := by
  constructor
  · rintro ⟨hvalid, hK, letters, hletters⟩
    exact ⟨hvalid, hK, List.ofFn letters, by simp, hletters⟩
  · rintro ⟨hvalid, hK, w, hlen, hw⟩
    have htake : (w.take x.2.2).length = x.2.2 := by simp [Nat.min_eq_left hlen]
    let letters : Fin x.2.2 → Fin x.1 :=
      fun i ↦ (w.take x.2.2)[i.val]'(by rw [htake]; exact i.isLt)
    have heq : List.ofFn letters = w.take x.2.2 := by
      apply List.ext_getElem
      · simpa using htake.symm
      · intro i hi hj
        simp [letters]
    refine ⟨hvalid, hK, letters, ?_⟩
    intro s hs
    rw [heq]
    exact ((List.take_sublist x.2.2 w).map Fin.val).trans (hw s hs)

theorem CommonSuperstring.commonSupersequence {x : CommonInput}
    (h : CommonSuperstring x) : CommonSupersequence x := by
  rcases h with ⟨hvalid, hK, n, letters, hw⟩
  exact ⟨hvalid, hK, n, letters, fun s hs ↦ (hw s hs).sublist⟩

end Computability.StringProblems
