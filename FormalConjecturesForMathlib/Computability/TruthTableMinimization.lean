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

public import FormalConjecturesForMathlib.Computability.BooleanCircuit
public import FormalConjecturesForMathlib.Computability.BooleanBranchingProgram
public import FormalConjecturesForMathlib.Computability.DeMorganFormula

/-!
# Truth-table minimization predicates

The input contains the entire table, not a circuit description or a sparse list
of samples. Its length is $2^n$; invalid table lengths are rejected by equality
or pointwise agreement. Arity and ordinary thresholds have binary encodings.
Only partial MCSP uses a unary threshold, following Hirahara's Definition 8.4.

Model definitions and primary sources are in the imported modules. These predicates
are independent of any proposed algorithm or unproved complexity statement.
-/

@[expose] public section

namespace TruthTableMinimization

open BooleanTruthTable

/-- Arity, complete Boolean truth table, binary size bound. -/
abbrev FullInput := ℕ × List Bool × ℕ

/-- Arity, complete partial truth table, unary size bound (Hirahara). -/
abbrev PartialCircuitInput := ℕ × List PartialBit × UnarySize

/-- Arity, complete partial truth table, binary size bound (Glinskih–Riazanov). -/
abbrev PartialBranchingInput := ℕ × List PartialBit × ℕ

/-- MCSP on De Morgan circuits, counting AND/OR gates and allowing free NOT gates. -/
def MinimumCircuit (x : FullInput) : Prop :=
  ∃ c : BooleanCircuit.Circuit (Fin x.1),
    c.size ≤ x.2.2 ∧ ofFunction (BooleanCircuit.Circuit.eval c) = x.2.1

/-- Partial MCSP: some small circuit agrees with every defined table entry. -/
def PartialMinimumCircuit (x : PartialCircuitInput) : Prop :=
  ∃ c : BooleanCircuit.Circuit (Fin x.1),
    c.size ≤ x.2.2.value ∧ Agrees x.2.1 (ofFunction (BooleanCircuit.Circuit.eval c))

/-- MFSP on De Morgan trees, counting only nonconstant leaves. -/
def MinimumFormula (x : FullInput) : Prop :=
  ∃ f : DeMorganFormula.Formula (Fin x.1),
    f.size ≤ x.2.2 ∧ ofFunction (fun v => f.eval v) = x.2.1

/-- Partial MBPSP, counting all nodes, including both sinks. -/
def PartialMinimumBranchingProgram (x : PartialBranchingInput) : Prop :=
  ∃ p : BooleanBranchingProgram.Program x.1,
    p.size ≤ x.2.2 ∧ Agrees x.2.1 (ofFunction p.eval)

/-- Full-truth-table Min-DNF, counting terms rather than literals. -/
def MinimumDNF (x : FullInput) : Prop :=
  ∃ d : DeMorganFormula.DNF (Fin x.1),
    d.size ≤ x.2.2 ∧ ofFunction (fun v => d.eval v) = x.2.1

theorem MinimumCircuit.table_length {x : FullInput} (h : MinimumCircuit x) :
    x.2.1.length = 2 ^ x.1 := by
  obtain ⟨c, _, hc⟩ := h
  rw [← hc, length_ofFunction]

theorem PartialMinimumCircuit.table_length {x : PartialCircuitInput}
    (h : PartialMinimumCircuit x) : x.2.1.length = 2 ^ x.1 := by
  obtain ⟨c, _, hc⟩ := h
  exact hc.length_eq.trans (length_ofFunction _)

theorem MinimumFormula.table_length {x : FullInput} (h : MinimumFormula x) :
    x.2.1.length = 2 ^ x.1 := by
  obtain ⟨f, _, hf⟩ := h
  rw [← hf, length_ofFunction]

theorem PartialMinimumBranchingProgram.table_length {x : PartialBranchingInput}
    (h : PartialMinimumBranchingProgram x) : x.2.1.length = 2 ^ x.1 := by
  obtain ⟨p, _, hp⟩ := h
  exact hp.length_eq.trans (length_ofFunction _)

theorem MinimumDNF.table_length {x : FullInput} (h : MinimumDNF x) :
    x.2.1.length = 2 ^ x.1 := by
  obtain ⟨d, _, hd⟩ := h
  rw [← hd, length_ofFunction]

/-- A fully specified partial table recovers exactly the full-circuit predicate. -/
theorem partialMinimumCircuit_values (n : ℕ) (table : List Bool) (s : ℕ) :
    PartialMinimumCircuit (n, table.map PartialBit.value, ⟨s⟩) ↔
      MinimumCircuit (n, table, s) := by
  simp only [PartialMinimumCircuit, MinimumCircuit, agrees_values, eq_comm]

/-- Padding makes the literal "size s" and "size at most s" readings equivalent. -/
theorem partialMinimumCircuit_iff_exact (x : PartialCircuitInput) :
    PartialMinimumCircuit x ↔
      ∃ c : BooleanCircuit.Circuit (Fin x.1), c.size = x.2.2.value ∧
        Agrees x.2.1 (ofFunction (BooleanCircuit.Circuit.eval c)) := by
  constructor
  · rintro ⟨c, hc, ht⟩
    refine ⟨c.padMany (x.2.2.value - c.size), ?_, ?_⟩
    · simp [Nat.add_sub_of_le hc]
    · have he : BooleanCircuit.Circuit.eval (c.padMany (x.2.2.value - c.size)) =
          BooleanCircuit.Circuit.eval c := by
        funext v
        exact BooleanCircuit.Program.eval_padMany c _ v Fin.elim0
      rw [he]
      exact ht
  · rintro ⟨c, hc, ht⟩
    exact ⟨c, hc.le, ht⟩

end TruthTableMinimization
