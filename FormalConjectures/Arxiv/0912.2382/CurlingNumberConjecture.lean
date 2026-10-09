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
module

public import FormalConjecturesUtil

/-!
# The Curling Number Conjecture

*Reference:* [arxiv/0912.2382](https://arxiv.org/abs/0912.2382)
**The Curling Number Conjecture**
by *Benjamin Chaffin and N. J. A. Sloane*
-/

@[expose] public section

namespace Arxiv.«0912.2382»

/--
The curling number

Let $S$ be a finite nonempty sequence of integers. By grouping adjacent terms, it is always possible
to write it as $S = X Y Y . . . Y = X Y^k$, where $X$ and $Y$ are sequences of integers and $Y$ is nonempty
($X$ is allowed to be the empty sequence $∅$). There may be several ways to do this: choose the one
that maximizes the value of $k$: this $k$ is the curling number of $S$, denoted by $k S$.
-/
noncomputable def k (S : List ℤ) : ℕ :=
  sSup {k : ℕ | ∃ X Y : List ℤ, Y ≠ [] ∧ S = X ++ (List.replicate k Y).flatten}


/-- A nonempty suffix repeated $r$ times uses at least $r$ entries. -/
@[category API, AMS 11]
theorem exponent_le_length {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ [])
    (hL : L = X ++ (List.replicate r Y).flatten) : r ≤ L.length := by
  have hlen := congrArg List.length hL
  simp at hlen
  have hpos : 1 ≤ Y.length := Nat.succ_le_of_lt (List.length_pos_iff.mpr hY)
  have hmul := Nat.mul_le_mul_left r hpos
  simp only [Nat.mul_one] at hmul
  omega

/-- The admissible repetition counts in the definition of $k(L)$ are bounded. -/
@[category API, AMS 11]
theorem bddAbove_exponents (L : List ℤ) :
    BddAbove {r : ℕ | ∃ X Y : List ℤ, Y ≠ [] ∧ L = X ++ (List.replicate r Y).flatten} := by
  refine ⟨L.length, ?_⟩
  rintro r ⟨X, Y, hY, hL⟩
  exact exponent_le_length hY hL

/-- The curling number cannot exceed the length of the sequence, including the empty case. -/
@[category API, AMS 11]
theorem k_le_length (L : List ℤ) : k L ≤ L.length := by
  apply csSup_le (show ∃ r : ℕ, ∃ X Y : List ℤ,
    Y ≠ [] ∧ L = X ++ (List.replicate r Y).flatten from ⟨0, L, [0], by simp, by simp⟩)
  rintro r ⟨X, Y, hY, hL⟩
  exact exponent_le_length hY hL

/-- Every nonempty sequence has curling number at least $1$. -/
@[category API, AMS 11]
theorem one_le_k {L : List ℤ} (hL : L ≠ []) : 1 ≤ k L := by
  exact le_csSup (bddAbove_exponents L) ⟨[], L, hL, by simp⟩

/-- A nonempty sequence has a suffix repeated exactly its curling number of times. -/
@[category API, AMS 11]
theorem k_attained {L : List ℤ} (hL : L ≠ []) :
    ∃ X Y : List ℤ, Y ≠ [] ∧ L = X ++ (List.replicate (k L) Y).flatten := by
  have hne : ({r : ℕ | ∃ X Y : List ℤ,
      Y ≠ [] ∧ L = X ++ (List.replicate r Y).flatten}).Nonempty :=
    ⟨1, [], L, hL, by simp⟩
  exact Nat.sSup_mem hne (bddAbove_exponents L)


/--
One starts with any initial
sequence of integers $S₀$, and extends it by repeatedly appending the curling number of the current
sequence.
-/
noncomputable def S (S₀ : List ℤ) (n : ℕ) : List ℤ :=
  match n with
  | 0 => S₀
  | n + 1 => (S S₀ n) ++ [Int.ofNat (k (S S₀ n))]

/-- Each extension step appends exactly one integer. -/
@[category API, AMS 11]
theorem S_length (L : List ℤ) (n : ℕ) : (S L n).length = L.length + n := by
  induction n with
  | zero => simp [S]
  | succ n ih => simp [S, ih, Nat.add_assoc]

/-- Extending a nonempty initial sequence preserves nonemptiness. -/
@[category API, AMS 11]
theorem S_ne_nil {L : List ℤ} (hL : L ≠ []) (n : ℕ) : S L n ≠ [] := by
  have hpos := List.length_pos_iff.mpr hL
  have hlen := S_length L n
  intro h
  simp only [h, List.length_nil] at hlen
  omega

/-- A one-term sequence has curling number $1$, regardless of the integer in it. -/
@[category test, AMS 11]
theorem k_singleton (a : ℤ) : k [a] = 1 := by
  have hle := k_le_length [a]
  have hge := one_le_k (by simp : [a] ≠ [])
  simp only [List.length_singleton] at hle
  omega

/-- The conjecture holds immediately for every one-term starting sequence. -/
@[category textbook, AMS 11]
theorem curling_number_conjecture_singleton (a : ℤ) : ∃ m, k (S [a] m) = 1 := by
  exact ⟨0, k_singleton a⟩

/--
Starting from any nonempty finite integer sequence, repeatedly appending its curling number
eventually gives a sequence with curling number $1$ [Chaffin and Sloane, Conjecture 1].
-/
@[category research open, AMS 11]
theorem curling_number_conjecture (S₀ : List ℤ) (h : S₀ ≠ []) : ∃ m, k (S S₀ m) = 1 := by
  sorry

end Arxiv.«0912.2382»
