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

public import FormalConjecturesForMathlib.Computability.CircuitFamilies
public meta import FormalConjecturesForMathlib.Computability.CircuitFamilies
public import FormalConjecturesForMathlib.Computability.TimeClasses
public import FormalConjecturesForMathlib.Computability.PolynomialHierarchy
public import FormalConjecturesForMathlib.Computability.AdviceClasses
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# Boundary and semantic tests for nonuniform complexity

These tests import supporting definitions only, not any admitted research statement.
-/

@[expose] public section

namespace NonuniformComplexityTest

open ComplexityTheory BooleanCircuit

example : (BooleanFamilyCircuit.const 0 false).eval Fin.elim0 = false := rfl
example : (BooleanFamilyCircuit.const 0 true).eval Fin.elim0 = true := rfl
example : (BooleanFamilyCircuit.const 0 true).size = 0 := rfl
example : (BooleanFamilyCircuit.const 3 false).eval (fun _ => true) = false := rfl
example : BooleanFamilyCircuit.eval (BooleanFamilyCircuit.const 0 true).neg Fin.elim0 =
    false := rfl

/-- Input projection uses a variable reference, not a hardwired reference. -/
def projection : BooleanFamilyCircuit 2 := .output (.inl (.inr 1))

example : projection.eval ![false, true] = true := rfl
example : projection.eval ![true, false] = false := rfl
example : projection.size = 0 := rfl

/-- The AND output is referenced twice by the OR gate, with unrestricted sharing. -/
def shared : BooleanFamilyCircuit 2 :=
  .step (.and (.inl (.inr 0)) (.inl (.inr 1)))
    (.step (.or (.inr 0) (.inr 0)) (.output (.inr 0)))

example : shared.size = 2 := rfl
example : shared.eval ![true, true] = true := rfl
example : shared.eval ![true, false] = false := rfl
example : shared.eval ![false, true] = false := rfl
example : shared.eval ![false, false] = false := rfl
example : shared.neg.size = 2 := rfl
example : BooleanFamilyCircuit.eval shared.neg ![false, true] = true := rfl

example (b : ℕ → Bool) : (fun x => b x.length) ∈ Ppoly := length_mem_Ppoly b
example : (fun _ => true) ∈ Ppoly := length_mem_Ppoly (fun _ => true)
example : (fun _ => false) ∈ Ppoly := length_mem_Ppoly (fun _ => false)
example (L : DecisionProblem) : Lᶜ ∈ Ppoly ↔ L ∈ Ppoly := mem_Ppoly_compl L

/-- The empty language has a zero-size circuit at every length, including zero. -/
theorem emptyLanguage_hasCircuits : HasCircuitSize (fun _ => false) (fun _ => 0) :=
  hasCircuitSize_length (fun _ => false)

/-- The full language also has a zero-size circuit family. -/
theorem fullLanguage_hasCircuits : HasCircuitSize (fun _ => true) (fun _ => 0) :=
  hasCircuitSize_length (fun _ => true)

example (n : ℕ) : AlternatingBlocks n true 0 (fun ws => ws = []) := rfl
example (n : ℕ) : AlternatingBlocks n false 0 (fun ws => ws = []) := rfl
example (n k : ℕ) (b : Bool) : AlternatingBlocks n b k (fun _ => True) := by simp
example (n k : ℕ) (b : Bool) : ¬ AlternatingBlocks n b k (fun _ => False) := by simp
example : AlternatingBlocks 0 true 3 (fun ws => ws = [[], [], []]) := by simp
example : AlternatingBlocks 0 false 3 (fun ws => ws = [[], [], []]) := by simp

/-- Equality between the first two quantified blocks. -/
def blocksEqual (ws : List (List Bool)) : Prop :=
  ws[0]?.getD [] = ws[1]?.getD []

/-- In forall-exists, the second block may copy the first. -/
theorem universal_existential_copy : AlternatingBlocks 1 false 2 blocksEqual := by
  intro v
  exact ⟨v, rfl⟩

/-- In exists-forall, a fixed one-bit string cannot equal both possible later strings. -/
theorem not_existential_universal_copy : ¬ AlternatingBlocks 1 true 2 blocksEqual := by
  rintro ⟨v, hv⟩
  have h0 := hv (fun _ => false)
  have h1 := hv (fun _ => true)
  simp [AlternatingBlocks, blocksEqual, List.ofFn_succ] at h0 h1
  simp [h0] at h1

example : AlternatingBlocks 0 true 2 blocksEqual := by simp [blocksEqual]
example : AlternatingBlocks 0 false 2 blocksEqual := by simp [blocksEqual]

/-- Blocks reach the verifier in quantifier order, not in reverse order. -/
theorem three_block_order : AlternatingBlocks 1 true 3
    (fun ws => ws[0]?.getD [] = [true] ∧ ws[2]?.getD [] = ws[1]?.getD []) := by
  refine ⟨fun _ => true, fun v => ⟨v, ?_⟩⟩
  simp [AlternatingBlocks, List.ofFn_succ]

/-- Every block has exactly the specified length, and exactly k blocks are passed. -/
theorem exact_block_shape (n k : ℕ) (b : Bool) :
    AlternatingBlocks n b k (fun ws => ws.length = k ∧ ∀ w ∈ ws, w.length = n) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    have h (v : Fin n → Bool) :
        AlternatingBlocks n (!b) k
          (fun ws => (List.ofFn v :: ws).length = k + 1 ∧
            ∀ w ∈ List.ofFn v :: ws, w.length = n) :=
      (ih (!b)).mono (by intro ws hws; simpa using hws)
    cases b
    · exact fun v => h v
    · exact ⟨fun _ => false, h _⟩

example : SigmaP 0 = P := rfl
example : PiP 0 = P := rfl
example : SigmaP 1 = QuantifiedPolyTime true 1 := rfl
example : SigmaP 2 = QuantifiedPolyTime true 2 := rfl
example : PiP 2 = QuantifiedPolyTime false 2 := rfl
example (k : ℕ) : SigmaP k ⊆ PH := sigmaP_subset_PH k

/-- This witness is the actual one-step identity TM2, not abstract decidability. -/
theorem identity_exponential_time : IsExpTime (id : List Bool → List Bool) :=
  isPolyTime_id.isExpTime

example : P ⊆ EXP := P_subset_EXP
example : 2 ^ (Polynomial.C 0).eval (0 : ℕ) = 1 := by norm_num
example : 2 ^ (Polynomial.X + Polynomial.C 1).eval (3 : ℕ) = 16 := by norm_num
example : 2 ^ (Polynomial.X ^ 2).eval (3 : ℕ) = 512 := by norm_num

example : ∃ w : List Bool, w.length ≤ 2 ^ (Polynomial.C 0).eval (0 : ℕ) ∧
    w = [true] := by
  exact ⟨[true], by norm_num, rfl⟩

example : ¬ ∃ w : List Bool, w.length ≤ 2 ^ (Polynomial.C 0).eval (0 : ℕ) ∧
    w = [true, true] := by
  simp

example : PolynomialAdvice (fun _ => []) := polynomialAdvice_const []
example (b : ℕ → Bool) : PolynomialAdvice (fun n => [b n]) :=
  polynomialAdvice_singleton b
example : PolynomialAdvice (fun n => List.replicate (n + 1) true) := by
  refine ⟨Polynomial.X + Polynomial.C 1, ?_⟩
  intro n
  simp

example (a : ℕ → List Bool) : a ([true, false] : List Bool).length =
    a ([false, true] : List Bool).length := rfl
example (A : DecisionProblem) (a : ℕ → List Bool) :
    withAdvice A a [] = A (BitstringEncoding.bitEncode (([] : List Bool), a 0)) := rfl
example (A : DecisionProblem) (a : ℕ → List Bool) :
    withAdvice Aᶜ a = (withAdvice A a)ᶜ := rfl

/-- The pairing preserves both the original input and the advice bits. -/
theorem advice_pair_injective {x y a b : List Bool}
    (h : BitstringEncoding.bitEncode (x, a) = BitstringEncoding.bitEncode (y, b)) :
    x = y ∧ a = b := by
  exact Prod.mk.inj (BitstringEncoding.bitEncode_injective h)

example (A : DecisionProblem) (a : ℕ → List Bool) (hA : A ∈ NP)
    (ha : PolynomialAdvice a) : withAdvice A a ∈ NPpoly :=
  withAdvice_mem hA ha

example {C D : ComplexityClass} (h : C ⊆ D) :
    WithPolyAdvice C ⊆ WithPolyAdvice D := WithPolyAdvice.mono h

#guard projection.eval ![false, true]
#guard !shared.eval ![true, false]
#guard (BooleanFamilyCircuit.const 0 true).eval Fin.elim0

end NonuniformComplexityTest
