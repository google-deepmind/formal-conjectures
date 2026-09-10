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

public import FormalConjecturesForMathlib.Computability.BooleanSatisfiability
public import FormalConjecturesForMathlib.Computability.PromiseProblems
public import Mathlib.Tactic.Linarith

/-!
# Gap satisfiability with a variable-count clock

Clauses and repeated occurrences retain their input multiplicities. Assignments
range over the distinct variable names actually represented in the input. The
yes region is perfect satisfiability; the no region bounds the satisfied-clause
fraction for every assignment. Empty formulas are excluded from both regions.

Reference: Allender–Farach-Colton–Tsai, *Syntactic Separation of Subset
Satisfiability Problems*, APPROX/RANDOM 2019, Conjecture 1, p.16:2:
https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.16.
We use a deterministic finite TM2 machine, a reciprocal positive exponential
rate, and a polynomial encoded-input factor. The exponent counts variables,
not clauses, occurrences, the largest variable name, or the encoding length.
-/

@[expose] public section

namespace Computability.GapSatisfiability

open BooleanSatisfiability ComplexityTheory

/-- Count satisfied clause positions, including repetitions. -/
def satisfied (formula : Formula) (chosen : Finset ℕ) : ℕ :=
  (formula.filter (fun clause => (clause.map (evalLiteral chosen)).any id)).length

theorem satisfied_le (formula : Formula) (chosen : Finset ℕ) :
    satisfied formula chosen ≤ formula.length := List.length_filter_le _ _

theorem satisfied_eq_length_iff (formula : Formula) (chosen : Finset ℕ) :
    satisfied formula chosen = formula.length ↔
      ∀ clause ∈ formula, (clause.map (evalLiteral chosen)).any id = true := by
  exact List.length_filter_eq_length_iff

/-- Perfect clause satisfaction agrees with the existing SAT semantics. -/
theorem satisfiable_iff (formula : Formula) :
    SatisfiableWith (fun values => values.any id) formula ↔
      ∃ chosen ⊆ support formula, satisfied formula chosen = formula.length := by
  simp only [SatisfiableWith, satisfied_eq_length_iff]

/-- Nonempty 3-CNF, with at most three literals per clause. -/
def Valid (formula : Formula) : Prop :=
  0 < formula.length ∧ ∀ clause ∈ formula, clause.length ≤ 3

instance (formula : Formula) : Decidable (Valid formula) := by
  unfold Valid
  infer_instance

def Yes (formula : Formula) : Prop :=
  Valid formula ∧ SatisfiableWith (fun values => values.any id) formula

/-- At most a (1 - epsilon) fraction of clauses is simultaneously satisfiable. -/
def No (ε : ℚ) (formula : Formula) : Prop :=
  Valid formula ∧ ∀ chosen ⊆ support formula,
    (satisfied formula chosen : ℚ) ≤ (1 - ε) * formula.length

instance (formula : Formula) : Decidable (Yes formula) := by
  unfold Yes
  infer_instance

instance (ε : ℚ) (formula : Formula) : Decidable (No ε formula) := by
  unfold No
  infer_instance

theorem yes_not_no {ε : ℚ} (hε : 0 < ε) {formula : Formula}
    (hy : Yes formula) : ¬ No ε formula := by
  intro hn
  obtain ⟨chosen, hc, hs⟩ := (satisfiable_iff formula).mp hy.2
  have hbound := hn.2 chosen hc
  rw [hs] at hbound
  have hm : (0 : ℚ) < formula.length := by exact_mod_cast hy.1.1
  nlinarith

/-- A fixed exponential rate, with arbitrary polynomial input-reading overhead. -/
def HasExponentialSeparator (ε : ℚ) (b : ℕ) : Prop :=
  ∃ C k : ℕ, 0 < C ∧ HasTimeSeparator Yes (No ε)
    (fun formula => C * ((BitstringEncoding.bitEncode formula).length + 1) ^ k *
      2 ^ ((support formula).card / b))

end Computability.GapSatisfiability
