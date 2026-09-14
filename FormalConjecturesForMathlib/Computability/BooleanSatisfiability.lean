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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.List.Count

/-!
# Encoded Boolean satisfiability variants

A literal consists of a binary natural-number variable name and a polarity: true means
positive and false means negated. Formulas are explicit lists of clauses. Only variable
names that occur in the formula are enumerated; their numerical magnitudes do not specify
an implicit variable universe. Literal occurrences, including repetitions, are preserved.

The three-literal relations for exactly-one and not-all-equal are those of Schaefer,
*The Complexity of Satisfiability Problems* (1978), pp. 216–218,
https://doi.org/10.1145/800133.804350. We distinguish the positive-variable relations from
their signed extensions (Garey–Johnson, *Computers and Intractability*, 1979,
LO3/LO4, p. 259). These use exactly three argument occurrences, as in the truth
tables on p. 218, rather than the set-based variants on p. 217. Ordinary 3-SAT uses at
most three literals, as in Karp (1972), item 11, p. 95,
https://doi.org/10.1007/978-1-4684-2001-2_9.

Decidability is by exhaustive finite search, not a polynomial-time algorithm.
-/

@[expose] public section

namespace Computability.BooleanSatisfiability

/-- A binary variable name and its polarity. -/
abbrev Literal := ℕ × Bool

/-- Explicit clauses of signed literal occurrences. -/
abbrev Formula := List (List Literal)

/-- Positive clauses have no polarity field. -/
abbrev PositiveFormula := List (List ℕ)

/-- The finite set of variable names actually occurring in the formula. -/
def support (formula : Formula) : Finset ℕ :=
  (formula.flatten.map Prod.fst).toFinset

theorem mem_support {formula : Formula} {clause : List Literal} {literal : Literal}
    (hc : clause ∈ formula) (hl : literal ∈ clause) : literal.1 ∈ support formula := by
  simp only [support, List.mem_toFinset, List.mem_map, List.mem_flatten]
  exact ⟨literal, ⟨clause, hc, hl⟩, rfl⟩

/-- A finite set records the variables assigned true. -/
def evalLiteral (chosen : Finset ℕ) (literal : Literal) : Bool :=
  decide (literal.1 ∈ chosen) == literal.2

/-- Every clause's list of literal values is accepted by a fixed Boolean relation. -/
def SatisfiableWith (accept : List Bool → Bool) (formula : Formula) : Prop :=
  ∃ chosen ⊆ support formula, ∀ clause ∈ formula,
    accept (clause.map (evalLiteral chosen)) = true

instance (accept : List Bool → Bool) (formula : Formula) :
    Decidable (SatisfiableWith accept formula) := by
  unfold SatisfiableWith
  infer_instance

/-- Restricting an assignment to the represented variables does not change a literal value. -/
theorem evalLiteral_restrict (assignment : ℕ → Bool) {formula : Formula} {literal : Literal}
    (h : literal.1 ∈ support formula) :
    evalLiteral ((support formula).filter (fun v ↦ assignment v = true)) literal =
      (assignment literal.1 == literal.2) := by
  simp [evalLiteral, h]

/-- Finite-support witnesses express the usual existence of a Boolean assignment to names. -/
theorem satisfiableWith_iff (accept : List Bool → Bool) (formula : Formula) :
    SatisfiableWith accept formula ↔ ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, accept (clause.map (fun l ↦ assignment l.1 == l.2)) = true := by
  constructor
  · rintro ⟨chosen, _, h⟩
    exact ⟨fun v ↦ decide (v ∈ chosen), h⟩
  · rintro ⟨assignment, h⟩
    refine ⟨(support formula).filter (fun v ↦ assignment v = true),
      Finset.filter_subset _ _, fun clause hc ↦ ?_⟩
    have values : clause.map (evalLiteral ((support formula).filter
        (fun v ↦ assignment v = true))) =
        clause.map (fun l ↦ assignment l.1 == l.2) := by
      apply List.map_congr_left
      intro literal hl
      exact evalLiteral_restrict assignment (mem_support hc hl)
    rw [values]
    exact h clause hc

/-- Every clause has exactly three argument occurrences. -/
def ExactlyThree (formula : Formula) : Prop :=
  ∀ clause ∈ formula, clause.length = 3

instance (formula : Formula) : Decidable (ExactlyThree formula) := by
  unfold ExactlyThree
  infer_instance

/-- Ordinary satisfiability with at most three signed literals per clause. -/
def ThreeSat (formula : Formula) : Prop :=
  (∀ clause ∈ formula, clause.length ≤ 3) ∧ SatisfiableWith (fun values ↦ values.any id) formula

instance (formula : Formula) : Decidable (ThreeSat formula) := by
  unfold ThreeSat
  infer_instance

/-- Exactly one true literal occurrence in each three-literal clause; negations are allowed. -/
def OneInThree (formula : Formula) : Prop :=
  ExactlyThree formula ∧ SatisfiableWith (fun values ↦ decide (values.count true = 1)) formula

instance (formula : Formula) : Decidable (OneInThree formula) := by
  unfold OneInThree
  infer_instance

/-- Both a true and a false literal in each three-literal clause; negations are allowed. -/
def NotAllEqual (formula : Formula) : Prop :=
  ExactlyThree formula ∧
    SatisfiableWith (fun values ↦ values.any id && values.any Bool.not) formula

instance (formula : Formula) : Decidable (NotAllEqual formula) := by
  unfold NotAllEqual
  infer_instance

/-- Embed a positive formula without changing its clause positions or argument occurrences. -/
def positiveEmbedding (formula : PositiveFormula) : Formula :=
  formula.map (fun clause ↦ clause.map (fun v ↦ (v, true)))

/-- Exactly one true variable occurrence in each positive three-variable clause. -/
def PositiveOneInThree (formula : PositiveFormula) : Prop :=
  OneInThree (positiveEmbedding formula)

instance (formula : PositiveFormula) : Decidable (PositiveOneInThree formula) := by
  unfold PositiveOneInThree
  infer_instance

/-- Both truth values occur in each positive three-variable clause. -/
def PositiveNotAllEqual (formula : PositiveFormula) : Prop :=
  NotAllEqual (positiveEmbedding formula)

instance (formula : PositiveFormula) : Decidable (PositiveNotAllEqual formula) := by
  unfold PositiveNotAllEqual
  infer_instance

/-- Direct assignment semantics for Schaefer's positive exactly-one relation. -/
theorem positiveOneInThree_iff (formula : PositiveFormula) :
    PositiveOneInThree formula ↔ (∀ clause ∈ formula, clause.length = 3) ∧
      ∃ assignment : ℕ → Bool, ∀ clause ∈ formula, (clause.map assignment).count true = 1 := by
  simp [PositiveOneInThree, OneInThree, ExactlyThree, positiveEmbedding, satisfiableWith_iff,
    List.map_map, Function.comp_def]

/-- Direct assignment semantics for Schaefer's positive not-all-equal relation. -/
theorem positiveNotAllEqual_iff (formula : PositiveFormula) :
    PositiveNotAllEqual formula ↔ (∀ clause ∈ formula, clause.length = 3) ∧
      ∃ assignment : ℕ → Bool, ∀ clause ∈ formula,
        (∃ v ∈ clause, assignment v = true) ∧ (∃ v ∈ clause, assignment v = false) := by
  simp [PositiveNotAllEqual, NotAllEqual, ExactlyThree, positiveEmbedding, satisfiableWith_iff,
    Function.comp_def]

end Computability.BooleanSatisfiability
