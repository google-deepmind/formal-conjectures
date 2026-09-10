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
import FormalConjecturesForMathlib.Computability.DecisionProblems
import FormalConjecturesForMathlib.Computability.TruthTableMinimization
import Mathlib.Tactic.NormNum

/-!
# Semantic tests for truth-table minimization

Kernel tests cover explicit row order, encodings, partial-row agreement, free
constants versus free negations, circuit sharing, both-sink size accounting,
repeated queries, and malformed table lengths. No open problem is imported.
-/

namespace TruthTableMinimizationTest

open BooleanTruthTable TruthTableMinimization DeMorganFormula

example : ofFunction (n := 0) (fun _ => true) = [true] := by decide +kernel
example : ofFunction (n := 1) (fun v => v 0) = [false, true] := by decide +kernel
example : ofFunction (n := 2) (fun v => v 0) = [false, false, true, true] := by
  decide +kernel
example : ofFunction (n := 2) (fun v => v 1) = [false, true, false, true] := by
  decide +kernel
example : ofFunction (n := 2) (fun v => v 0 && v 1) = [false, false, false, true] := by
  decide +kernel
example : ofFunction (n := 2) (fun v => v 0 ^^ v 1) = [false, true, true, false] := by
  decide +kernel
example : (assignments 6).length = 64 := by decide +kernel
example (n : ℕ) (f g : (Fin n → Bool) → Bool) (h : ofFunction f = ofFunction g) :
    f = g := ofFunction_injective h

example : BitstringEncoding.bitEncode (PartialBit.value false) = [false, false] := rfl
example : BitstringEncoding.bitEncode (PartialBit.value true) = [false, true] := rfl
example : BitstringEncoding.bitEncode PartialBit.star = [true, false] := rfl
example : BitstringEncoding.bitDecode (α := PartialBit) [true, true] = none := rfl
example : BitstringEncoding.bitDecode (α := PartialBit) [] = none := rfl
example : BitstringEncoding.bitDecode (α := PartialBit) [false] = none := rfl
example : BitstringEncoding.bitEncode (UnarySize.mk 0) = [] := rfl
example : BitstringEncoding.bitEncode (UnarySize.mk 3) = [true, true, true] := rfl
example : BitstringEncoding.bitDecode (α := UnarySize) [] = some ⟨0⟩ := rfl
example : BitstringEncoding.bitDecode (α := UnarySize) [true, false] = none := rfl
example : (BitstringEncoding.bitEncode (UnarySize.mk 32)).length = 32 := by decide +kernel
example (s : UnarySize) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode s) = some s := by simp
example (x : PartialCircuitInput) :
    BitstringEncoding.bitDecode (BitstringEncoding.bitEncode x) = some x := by simp

example : Agrees [.star, .value true] [false, true] := by decide +kernel
example : Agrees [.star, .value true] [true, true] := by decide +kernel
example : ¬ Agrees [.star, .value true] [false, false] := by decide +kernel
example : ¬ Agrees [.star] [false, true] := by decide +kernel
example : ¬ Agrees [.star, .star] [false] := by decide +kernel
example : ¬ Agrees [] [false] := by decide +kernel
example : Agrees [] [] := by decide +kernel

def andFormula : Formula (Fin 2) := .and (.literal (0, true)) (.literal (1, true))
def freeConstantFormula : Formula (Fin 1) :=
  .or (.and (.const true) (.const false)) (.const true)

example : andFormula.size = 2 := rfl
example : ofFunction (fun v => andFormula.eval v) = [false, false, false, true] := by
  decide +kernel
example : freeConstantFormula.size = 0 := rfl
example : ofFunction (fun v => freeConstantFormula.eval v) = [true, true] := by decide +kernel
example : andFormula.neg.size = 2 := by decide +kernel
example : ofFunction (fun v => andFormula.neg.eval v) = [true, true, true, false] := by
  decide +kernel
example : MinimumFormula (0, [false], 0) := ⟨.const false, by decide, rfl⟩
example : MinimumFormula (1, [true, true], 0) := ⟨freeConstantFormula, by decide, rfl⟩
example : MinimumFormula (2, [false, false, false, true], 2) :=
  ⟨andFormula, by decide, rfl⟩

theorem nonconstant_formula_needs_leaf : ¬ MinimumFormula (1, [false, true], 0) := by
  rintro ⟨f, hs, ht⟩
  have hc := f.eval_eq_of_size_zero (Nat.eq_zero_of_le_zero hs)
    (Fin.cons false Fin.elim0) (Fin.cons true Fin.elim0)
  change [f.eval (Fin.cons false Fin.elim0), f.eval (Fin.cons true Fin.elim0)] =
    [false, true] at ht
  obtain ⟨hf, ht'⟩ := List.cons.inj ht
  have ht'' := (List.cons.inj ht').1
  rw [hf, ht''] at hc
  cases hc

def xorDNF : DNF (Fin 2) := [[(0, true), (1, false)], [(0, false), (1, true)]]

example : xorDNF.size = 2 := rfl
example : ofFunction (fun v => xorDNF.eval v) = [false, true, true, false] := by decide +kernel
example : xorDNF.toFormula.size = 4 := rfl
example : ofFunction (fun v => xorDNF.toFormula.eval v) = [false, true, true, false] := by
  decide +kernel
example : MinimumDNF (2, [false, true, true, false], 2) := ⟨xorDNF, by decide, rfl⟩
example : MinimumDNF (0, [false], 0) := ⟨[], by decide, rfl⟩
example : MinimumDNF (0, [true], 1) := ⟨[[]], by decide, rfl⟩
example : ofFunction (n := 1) (fun v => DNF.eval v [[(0, false), (0, true)]]) =
    [false, false] := by decide +kernel
example : ofFunction (n := 1) (fun v => DNF.eval v [[(0, true), (0, true)]]) =
    [false, true] := by decide +kernel

theorem true_dnf_needs_term : ¬ MinimumDNF (0, [true], 0) := by
  rintro ⟨d, hs, ht⟩
  have hd : d = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hs)
  subst d
  simp [ofFunction, assignments, DNF.eval] at ht

open BooleanCircuit in
def xorCircuit : Circuit (Fin 2) :=
  .step (.and (.inl 0) (.inl 1))
    (.step (.or (.inl 0) (.inl 1))
      (.step (.not (.inr 1))
        (.step (.and (.inr 0) (.inr 1)) (.output (.inr 0)))))

open BooleanCircuit in
def falseCircuit : Circuit (Fin 1) :=
  .step (.not (.inl 0)) (.step (.and (.inl 0) (.inr 0)) (.output (.inr 0)))

open BooleanCircuit in
def sharedCircuit : Circuit (Fin 3) :=
  .step (.and (.inl 0) (.inl 1))
    (.step (.or (.inr 0) (.inl 2))
      (.step (.and (.inr 0) (.inr 1)) (.output (.inr 0))))

example : xorCircuit.size = 3 := rfl
example : xorCircuit.gateCount = 4 := rfl
example : ofFunction (BooleanCircuit.Circuit.eval xorCircuit) = [false, true, true, false] := by
  decide +kernel
example : MinimumCircuit (2, [false, true, true, false], 3) := ⟨xorCircuit, by decide, rfl⟩
example : MinimumCircuit (1, [false, true], 0) :=
  ⟨.output (.inl 0), by decide, rfl⟩
example : MinimumCircuit (1, [true, false], 0) :=
  ⟨(.output (.inl 0) : BooleanCircuit.Circuit (Fin 1)).neg, by decide, rfl⟩
example : falseCircuit.size = 1 := rfl
example : MinimumCircuit (1, [false, false], 1) := ⟨falseCircuit, by decide, rfl⟩
example : sharedCircuit.size = 3 := rfl
example : ofFunction (BooleanCircuit.Circuit.eval sharedCircuit) =
    [false, false, false, false, false, false, true, true] := by decide +kernel
example : xorCircuit.pad.size = 4 := rfl
example : (xorCircuit.padMany 7).size = 10 := by decide +kernel
example : ofFunction (BooleanCircuit.Circuit.eval (xorCircuit.padMany 7)) =
    [false, true, true, false] := by decide +kernel
example : ofFunction (BooleanCircuit.Circuit.eval xorCircuit.pad) =
    [false, true, true, false] := by decide +kernel
example : PartialMinimumCircuit (1, [.star, .star], ⟨0⟩) :=
  ⟨.output (.inl 0), by decide, by decide +kernel⟩
example (x : PartialCircuitInput) (h : PartialMinimumCircuit x) :
    ∃ c : BooleanCircuit.Circuit (Fin x.1), c.size = x.2.2.value ∧
      Agrees x.2.1 (ofFunction (BooleanCircuit.Circuit.eval c)) :=
  (partialMinimumCircuit_iff_exact x).mp h
example (table : List Bool) (s : ℕ) : ¬ MinimumCircuit (0, table, s) := by
  rintro ⟨c, _, _⟩
  exact BooleanCircuit.Circuit.not_nonempty_zero ⟨c⟩
example (table : List PartialBit) (s : UnarySize) : ¬ PartialMinimumCircuit (0, table, s) := by
  rintro ⟨c, _, _⟩
  exact BooleanCircuit.Circuit.not_nonempty_zero ⟨c⟩
example : PartialMinimumCircuit (1, [.value false, .star], ⟨0⟩) :=
  ⟨.output (.inl 0), by decide, by decide +kernel⟩
example : PartialMinimumCircuit (1, [.star, .value false], ⟨0⟩) :=
  ⟨(.output (.inl 0) : BooleanCircuit.Circuit (Fin 1)).neg, by decide, by decide +kernel⟩

def identityBP : BooleanBranchingProgram.Program 1 where
  count := 1
  nonempty := by decide
  query _ := 0
  low _ := 0
  high _ := 1
  low_lt := by decide +kernel
  high_lt := by decide +kernel
  incoming := by decide +kernel

/-- Both sinks are graph-reachable, but the 1-sink requires inconsistent queries. -/
def repeatedFalseBP : BooleanBranchingProgram.Program 1 where
  count := 2
  nonempty := by decide
  query _ := 0
  low q := if q.val = 0 then 1 else 0
  high q := if q.val = 0 then 0 else 2
  low_lt := by decide +kernel
  high_lt := by decide +kernel
  incoming := by decide +kernel

example : identityBP.size = 3 := rfl
example : ofFunction identityBP.eval = [false, true] := by decide +kernel
example : repeatedFalseBP.size = 4 := rfl
example : ofFunction repeatedFalseBP.eval = [false, false] := by decide +kernel
example : PartialMinimumBranchingProgram (1, [.value false, .value true], 3) :=
  ⟨identityBP, by decide, by decide +kernel⟩
example : PartialMinimumBranchingProgram (1, [.value false, .value false], 4) :=
  ⟨repeatedFalseBP, by decide, by decide +kernel⟩
example : PartialMinimumBranchingProgram (1, [.star, .star], 3) :=
  ⟨identityBP, by decide, by decide +kernel⟩

theorem bp_two_nodes_insufficient (table : List PartialBit) :
    ¬ PartialMinimumBranchingProgram (1, table, 2) := by
  rintro ⟨p, hp, _⟩
  change p.size ≤ 2 at hp
  have := p.three_le_size
  omega

example (table : List PartialBit) (s : ℕ) :
    ¬ PartialMinimumBranchingProgram (0, table, s) := by
  rintro ⟨p, _, _⟩
  exact BooleanBranchingProgram.Program.not_nonempty_zero ⟨p⟩

example : ¬ MinimumCircuit (2, [false, true], 100) := by
  intro h
  have := h.table_length
  norm_num at this
example : ¬ MinimumFormula (0, [], 100) := by
  intro h
  have := h.table_length
  norm_num at this
example : ¬ MinimumDNF (1, [false], 100) := by
  intro h
  have := h.table_length
  norm_num at this
example : ¬ PartialMinimumCircuit (1, [.star], ⟨100⟩) := by
  intro h
  have := h.table_length
  norm_num at this
example : ¬ PartialMinimumBranchingProgram (1, [.star], 100) := by
  intro h
  have := h.table_length
  norm_num at this

#guard ofFunction (BooleanCircuit.Circuit.eval xorCircuit) == [false, true, true, false]
#guard ofFunction repeatedFalseBP.eval == [false, false]
#guard BitstringEncoding.bitEncode (UnarySize.mk 3) == [true, true, true]

end TruthTableMinimizationTest
