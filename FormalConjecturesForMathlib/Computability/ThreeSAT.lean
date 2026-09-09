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
public import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Structured 3-CNF reference semantics

Variables are explicitly indexed by `Fin n`; each clause has at most three literals.
The empty conjunction is true and an empty clause is false. The reference checker exhausts
all assignments, including those of unused or sparsely occurring variable indices.

This module supplies reference semantics for structured formulas. A bitstring parser and
polynomial reductions to the existing complexity classes are separate developments.
For the surrounding SAT decision/search distinction, see Aaronson, *P =? NP*, §2.2.1,
https://www.scottaaronson.com/papers/pnp.pdf.
-/

@[expose] public section

namespace Computability.ThreeSAT

/-- A signed variable; `positive = false` denotes a negated variable. -/
structure Literal (n : ℕ) where
  index : Fin n
  positive : Bool
  deriving DecidableEq

/-- Clauses have at most three literals, including empty clauses. -/
structure Clause (n : ℕ) where
  literals : List (Literal n)
  length_le : literals.length ≤ 3
  deriving DecidableEq

abbrev Formula (n : ℕ) := List (Clause n)

variable {n : ℕ}

/-- Mathematical satisfiability, expressed using assignments and clause witnesses. -/
def Satisfiable (formula : Formula n) : Prop :=
  ∃ assignment : Fin n → Bool, ∀ clause ∈ formula,
    ∃ literal ∈ clause.literals, assignment literal.index = literal.positive

def eval (formula : Formula n) (assignment : Fin n → Bool) : Bool :=
  formula.all fun clause ↦ clause.literals.any fun literal ↦
    assignment literal.index == literal.positive

theorem eval_eq_true (formula : Formula n) (assignment : Fin n → Bool) :
    eval formula assignment = true ↔ ∀ clause ∈ formula,
      ∃ literal ∈ clause.literals, assignment literal.index = literal.positive := by
  simp [eval]

/-- Exhaustive reference evaluation over all $2^n$ assignments; no polynomial bound is claimed. -/
def referenceCheck (formula : Formula n) : Bool :=
  decide (∃ assignment : Fin n → Bool, eval formula assignment = true)

@[simp]
theorem referenceCheck_eq_true (formula : Formula n) :
    referenceCheck formula = true ↔ Satisfiable formula := by
  simp [referenceCheck, Satisfiable, eval_eq_true]

/-- Renaming variables transports assignments by composition. -/
def rename {m : ℕ} (f : Fin n → Fin m) (formula : Formula n) : Formula m :=
  formula.map fun clause ↦
    ⟨clause.literals.map (fun literal ↦ ⟨f literal.index, literal.positive⟩), by
      simpa using clause.length_le⟩

theorem eval_rename {m : ℕ} (f : Fin n → Fin m) (formula : Formula n)
    (assignment : Fin m → Bool) :
    eval (rename f formula) assignment = eval formula (assignment ∘ f) := by
  simp [rename, eval, Function.comp_def]

theorem satisfiable_rename_equiv {m : ℕ} (e : Fin n ≃ Fin m) (formula : Formula n) :
    Satisfiable (rename e formula) ↔ Satisfiable formula := by
  simp only [← referenceCheck_eq_true, referenceCheck, decide_eq_true_eq, eval_rename]
  constructor
  · rintro ⟨assignment, h⟩
    exact ⟨assignment ∘ e, h⟩
  · rintro ⟨assignment, h⟩
    refine ⟨assignment ∘ e.symm, ?_⟩
    simpa [Function.comp_def] using h

end Computability.ThreeSAT
