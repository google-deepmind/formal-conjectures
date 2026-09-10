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
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Polynomial hierarchy by alternating bounded quantifiers

A level has a fixed number of quantifier blocks. Each block ranges over all
bitstrings of the same polynomial length. The final predicate is computed by
one actual polynomial-time TM2 machine on the input and list of blocks.

Reference: Arora–Barak, author draft dated 2007-01-08, Definition 5.4 and §5.2.1:
https://theory.cs.princeton.edu/complexity/book.pdf.
-/

@[expose] public section

namespace ComplexityTheory

/-- Alternating quantifiers over k length-n blocks, in their original order.
The Boolean selects the first quantifier: true is existential. -/
def AlternatingBlocks (n : ℕ) : Bool → ℕ → (List (List Bool) → Prop) → Prop
  | _, 0, R => R []
  | true, k + 1, R =>
      ∃ v : Fin n → Bool, AlternatingBlocks n false k (fun ws => R (List.ofFn v :: ws))
  | false, k + 1, R =>
      ∀ v : Fin n → Bool, AlternatingBlocks n true k (fun ws => R (List.ofFn v :: ws))

@[simp]
theorem alternatingBlocks_zero (n : ℕ) (b : Bool) (R : List (List Bool) → Prop) :
    AlternatingBlocks n b 0 R ↔ R [] := by cases b <;> rfl

@[simp]
theorem alternatingBlocks_const (n k : ℕ) (b : Bool) (Q : Prop) :
    AlternatingBlocks n b k (fun _ => Q) ↔ Q := by
  induction k generalizing b with
  | zero => simp
  | succ k ih => cases b <;> simp [AlternatingBlocks, ih]

/-- A zero-length block is the unique empty bitstring, not an empty domain. -/
@[simp]
theorem alternatingBlocks_zero_length (k : ℕ) (b : Bool) (R : List (List Bool) → Prop) :
    AlternatingBlocks 0 b k R ↔ R (List.replicate k []) := by
  induction k generalizing b R with
  | zero => simp
  | succ k ih => cases b <;> simp [AlternatingBlocks, ih, List.replicate_succ]

/-- Expanding every terminal predicate preserves any alternating prefix. -/
theorem AlternatingBlocks.mono {n k : ℕ} {b : Bool}
    {R S : List (List Bool) → Prop} (h : AlternatingBlocks n b k R)
    (hRS : ∀ ws, R ws → S ws) : AlternatingBlocks n b k S := by
  induction k generalizing b R S with
  | zero => exact hRS [] h
  | succ k ih =>
    cases b
    · exact fun v => ih (h v) (fun ws => hRS (List.ofFn v :: ws))
    · obtain ⟨v, hv⟩ := h
      exact ⟨v, ih hv (fun ws => hRS (List.ofFn v :: ws))⟩

/-- Quantified polynomial-time languages with a prescribed prefix length. -/
def QuantifiedPolyTime (b : Bool) (k : ℕ) : Set DecisionProblem :=
  {L | ∃ (p : Polynomial ℕ) (R : (List Bool × List (List Bool)) → Bool),
    IsPolyTime R ∧ ∀ x, L x = true ↔
      AlternatingBlocks (p.eval x.length) b k (fun ws => R (x, ws) = true)}

/-- The existential levels; level zero is P. -/
def SigmaP : ℕ → Set DecisionProblem
  | 0 => P
  | k + 1 => QuantifiedPolyTime true (k + 1)

/-- The universal levels; level zero is P. -/
def PiP : ℕ → Set DecisionProblem
  | 0 => P
  | k + 1 => QuantifiedPolyTime false (k + 1)

/-- The union of all finite existential levels. -/
def PH : Set DecisionProblem := {L | ∃ k, L ∈ SigmaP k}

@[simp]
theorem sigmaP_zero : SigmaP 0 = P := rfl

@[simp]
theorem piP_zero : PiP 0 = P := rfl

theorem sigmaP_subset_PH (k : ℕ) : SigmaP k ⊆ PH :=
  fun _ h => ⟨k, h⟩

end ComplexityTheory
