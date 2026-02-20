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

import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases

open scoped Classical

/-! # Arithmetic Progressions

Main definitions:
- `Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α)` : predicate asserting that `s` is the
  set consisting of an arithmetic progression of length `l` (possibly infinite) with first term
  `a` and difference `d`. Useful for cases in which additional conditions need to be applied to
  the individual terms and/or difference.
- `Set.IsAPOfLength (s : Set α) (l : ℕ∞)` : predicate asserting that `s` is the set consisting
  of an arithmetic progression of length `l`, for some some first term and difference.
-/

variable {α : Type*} [AddCommMonoid α]

/--
A set $S$ is an arithmetic progression of length $l$ with first term $a$ and difference $d$
if $S = \{a, a + d, ..., a + (l - 1)d\}$, if $l$ if finite, else $S = \{a, a + d, a + 2d, ...\}.
This can be written as `Set.IsAPOfLengthWith a l a d`, where `l : ℕ∞` may take the infinite
value `⊤`.
-/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/--
A list version of `Set.IsAPOfLengthWith`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

namespace Set.IsAPOfLengthWith

variable {s : Set α} {l : ℕ∞} {a d : α}

theorem card (h : s.IsAPOfLengthWith l a d) : ENat.card s = l := h.1
theorem eq (h : s.IsAPOfLengthWith l a d) : s = {a + n • d | (n : ℕ) (_ : n < l)} := h.2

/-- An arithmetic progression with first term `a` and difference `d` is of length zero if and only
if `s` is empty. -/
@[simp]
theorem zero : s.IsAPOfLengthWith 0 a d ↔ s = ∅ := by simp [IsAPOfLengthWith]

/-- An arithmetic progression with first term `a` and difference `d` is of length one if and only
if `s` is a singleton. -/
@[simp]
theorem one : s.IsAPOfLengthWith 1 a d ↔ s = {a} := by simp +contextual [IsAPOfLengthWith]

end Set.IsAPOfLengthWith

namespace List.IsAPOfLengthWith

variable {s : List α} {l : ℕ} {a d : α}

theorem length (h : s.IsAPOfLengthWith l a d) : s.length = l := by
  cases h <;> simp_all

/-- An arithmetic progression with first term `a` and difference `d` is of length zero if and only
if `s` is empty. -/
@[simp]
theorem zero : s.IsAPOfLengthWith 0 a d ↔ s = [] := by
  simp [IsAPOfLengthWith]

/-- An arithmetic progression with first term `a` and difference `d` is of length one if and only
if `s` is a singleton. -/
@[simp]
theorem one : s.IsAPOfLengthWith 1 a d ↔ s = [a] := by
  simp [IsAPOfLengthWith]

end List.IsAPOfLengthWith

/-- In an abelian additive group `α`, the set `{a, b}` with `a ≠ b` is an arithmetic progression of
length `2` with first term `a` and difference `b - a`. -/
theorem Set.isAPOfLengthWith_pair {α : Type*} [DecidableEq α] [AddCommGroup α]
    {a b : α} (hab : a ≠ b) :
    Set.IsAPOfLengthWith {a, b} 2 a (b - a) := by
  simp [IsAPOfLengthWith]
  rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton])]
  simp
  refine Set.ext fun x => ⟨fun h ↦ ?_, fun ⟨n, ⟨_, _⟩⟩ ↦ by interval_cases n <;> simp_all⟩
  cases h with
  | inl hl => use 0; simp [hl]
  | inr hr => exact ⟨1, by norm_num, by simp_all⟩

-- Formalisation note: separate result needed for `ℕ` since this is not covered by
-- the `AddCommGroup` result above.
/-- The set `{a, b} : Set ℕ` with `a < b` is an arithmetic progression of length `2` with
first term `a` and difference `b - a`. -/
theorem Nat.isAPOfLengthWith_pair {a b : ℕ} (hab : a < b) :
    Set.IsAPOfLengthWith {a, b} 2 a (b - a) := by
  let ⟨n, h⟩ := Nat.exists_eq_add_of_lt hab
  simp [Set.IsAPOfLengthWith, h, add_assoc]
  exact Set.ext fun x => ⟨fun a => by aesop, fun ⟨w, ⟨_, _⟩⟩ => by interval_cases w <;> simp_all⟩

/--
The predicate that a set `s` is an arithmetic progression of length `l` (possibly infinite).
This predicate does not assert a specific value for the first term or the difference of the
arithmetic progression.
-/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/--
A list version of `Set.IsAPOfLength`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

namespace Set.IsAPOfLength

open Set.IsAPOfLengthWith

variable {s : Set α} {l : ℕ∞}

theorem card (h : s.IsAPOfLength l) : ENat.card s = l := h.choose_spec.choose_spec.1

theorem eq (h : s.IsAPOfLength l) : ∃ a d : α, s = {a + n • d | (n : ℕ) (_ : n < l)} :=
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2⟩

/-- Only the empty set is a finite arithmetic progression of length $0$. -/
@[simp] theorem zero : s.IsAPOfLength 0 ↔ s = ∅ := by simp [Set.IsAPOfLength]

/-- Only singletons are finite arithmetic progressions of length $1$. -/
@[simp] theorem one : s.IsAPOfLength 1 ↔ ∃ a, s = {a} := by simp [IsAPOfLength]

/-- If a set is an arithmetic progression of lengths `l₁` and `l₂`, then the lengths are
equal. -/
theorem congr {s : Set α} {l₁ l₂ : ℕ∞}
    (h₁ : s.IsAPOfLength l₁) (h₂ : s.IsAPOfLength l₂) :
    l₁ = l₂ := by
  rw [← h₁.card, h₂.card]

end Set.IsAPOfLength

namespace List.IsAPOfLength

open List.IsAPOfLengthWith

variable {s : List α} {l : ℕ}

theorem length (h : s.IsAPOfLength l) : s.length = l := by
  obtain ⟨_, _, h⟩ := h
  exact h.length

/-- Only the empty list is a finite arithmetic progression of length $0$. -/
@[simp] theorem zero : s.IsAPOfLength 0 ↔ s = [] := by simp [IsAPOfLength]

/-- Only singletons are finite arithmetic progressions of length $1$. -/
@[simp] theorem one : s.IsAPOfLength 1 ↔ ∃ a, s = [a] := by simp [IsAPOfLength]

/-- If a list is an arithmetic progression of lengths `l₁` and `l₂`, then the lengths are
equal. -/
theorem congr {s : List α} {l₁ l₂ : ℕ}
    (h₁ : s.IsAPOfLength l₁) (h₂ : s.IsAPOfLength l₂) :
    l₁ = l₂ := by
  rw [← h₁.length, h₂.length]

end List.IsAPOfLength

theorem Set.isAPOfLength_pair {α : Type*} [DecidableEq α] [AddCommGroup α] {a b : α} (hab : a ≠ b) :
    Set.IsAPOfLength {a, b} 2 :=
  ⟨a, b - a, Set.isAPOfLengthWith_pair hab⟩

theorem Nat.isAPOfLength_pair {a b : ℕ} (hab : a < b) :
    Set.IsAPOfLength {a, b} 2 :=
  ⟨a, b - a, Nat.isAPOfLengthWith_pair hab⟩

/-- The empty set is not an arithmetic progression of positive length. -/
theorem Set.not_isAPOfLength_empty {l : ℕ∞} (hl : 0 < l) :
    ¬Set.IsAPOfLength (∅ : Set α) l :=
  fun h ↦ by simp_all [h.congr <| Set.IsAPOfLength.zero.2 rfl]

/-- We say that a set `s` is free of arithmetic progressions of length `l` if `s` contains no
non-trivial arithmetic progressions of length `l`. Written as `Set.IsAPOfLengthFree s l`. --/
def Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1

/-- Any set is free of arithmetic progressions of length `1`, because such APs are all trivial. -/
theorem Set.isAPOfLengthFree_one (s : Set α) : s.IsAPOfLengthFree 1 := by
  simp [Set.IsAPOfLengthFree]

/-- Any set is free of arithmetic progressions of length `0`, because such APs are all trivial. -/
theorem Set.isAPOfLengthFree_zero (s : Set α) : s.IsAPOfLengthFree 0 := by
  simp [Set.IsAPOfLengthFree]

/-- Any non-trivial arithmetic progression cannot be free of arithmetic progressions. -/
theorem Set.IsAPOfLength.not_isAPOfLengthFree {s : Set α} {l : ℕ∞}
    (hs : s.IsAPOfLength l) (hl : 1 < l) : ¬s.IsAPOfLengthFree l := by
  simpa [Set.IsAPOfLengthFree] using ⟨s, le_rfl, ⟨hs, hl⟩⟩

/--
Define the largest possible size of a subset of $\{1, \dots, N\}$ that does not contain
any non-trivial $k$-term arithmetic progression.
-/
noncomputable def Set.IsAPOfLengthFree.maxCard (k : ℕ) (N : ℕ) : ℕ :=
  sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}

theorem Set.IsAPOfLengthFree.maxCard_zero (N : ℕ) : maxCard 0 N = N := by
  simp only [maxCard, Nat.cast_zero, isAPOfLengthFree_zero, exists_const, exists_prop]
  apply IsGreatest.csSup_eq
  refine ⟨⟨Finset.Icc 1 N, Subset.rfl, Nat.card_Icc _ _⟩, ?_⟩
  rintro n ⟨S, hS, rfl⟩
  exact S.card_mono hS |>.trans_eq (Nat.card_Icc _ _)

theorem Set.IsAPOfLengthFree.maxCard_one (N : ℕ) : maxCard 1 N = N := by
  nth_rw 2 [← maxCard_zero N]
  simp [maxCard, isAPOfLengthFree_one, isAPOfLengthFree_zero]

/-- A set `A` contains an arithmetic progression of length `k` with difference `d`. -/
def Set.ContainsAP (A : Set α) (k : ℕ) (d : α) : Prop :=
  ∃ a, ∃ s, s ⊆ A ∧ s.IsAPOfLengthWith (k : ℕ∞) a d

def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : Set α}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, ((·.1) '' ap).IsAPOfLength k ∧
    ∀ m ∈ ap, coloring m = c

/--
A function `f : α → β` has a monotone `k`-term arithmetic progression if there exists an
arithmetic progression `l` of length `k` in `α` such that its image under `f` is sorted.
-/
def HasMonotoneAP {β : Type*} [Preorder β] (f : α → β) (k : ℕ) : Prop :=
  ∃ l : List α, l.IsAPOfLength k ∧ (l.map f).Pairwise (· < ·)

/--
Define the largest possible size of a subset of a finset `s` that does not contain
any non-trivial `k`-term arithmetic progression.
-/
noncomputable def Finset.maxAPFreeCard (k : ℕ) (s : Finset α) : ℕ :=
  (s.powerset.filter fun t : Finset α ↦ (t : Set α).IsAPOfLengthFree k).sup Finset.card
