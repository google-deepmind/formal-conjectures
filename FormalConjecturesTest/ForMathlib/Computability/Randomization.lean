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
import FormalConjecturesForMathlib.Computability.PseudorandomGenerator
import FormalConjecturesForMathlib.Computability.ExactMatching
import FormalConjecturesForMathlib.Computability.DecisionProblems
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Semantic tests for randomization and exact matching

These kernel proofs check exact coin probabilities, error orientation, seed and
output lengths, simple circuit distinguishers, graph validity, and exact red counts.
No open conjecture is imported.
-/

namespace RandomizationTest

open ComplexityTheory RandomCoins BooleanCircuit Computability.MatrixGraph

def firstBit (r : List Bool) : Bool := r[0]?.getD false

def twoBitOr (r : List Bool) : Bool :=
  r[0]?.getD false || r[1]?.getD false

example : count 0 (fun r => r.isEmpty) = 1 := by decide
example : count 0 firstBit = 0 := by decide
example : probability 0 (fun r => r.isEmpty) = 1 := by
  norm_num [probability, show count 0 (fun r => r.isEmpty) = 1 by decide]

theorem firstBit_probability : probability 1 firstBit = 1 / 2 := by
  norm_num [probability, show count 1 firstBit = 1 by decide]

example : probability 2 firstBit = 1 / 2 := by
  norm_num [probability, show count 2 firstBit = 2 by decide]

theorem twoBitOr_probability : probability 2 twoBitOr = 3 / 4 := by
  norm_num [probability, show count 2 twoBitOr = 3 by decide]

example : probability 3 twoBitOr = 3 / 4 := by
  norm_num [probability, show count 3 twoBitOr = 6 by decide]
example : probability 2 (fun r => !twoBitOr r) = 1 / 4 := by
  norm_num [probability, show count 2 (fun r => !twoBitOr r) = 1 by decide]
example : count 2 (fun r => decide (r.length = 1)) = 0 := by decide
example : count 2 (fun r => decide (r.length = 2)) = 4 := by decide

example : BoundedError (Polynomial.C 2) (fun p => twoBitOr p.2) (fun _ => true) := by
  intro x
  simpa using (show (2 / 3 : ℚ) ≤ probability 2 twoBitOr by
    rw [twoBitOr_probability]; norm_num)

example : ¬ BoundedError (Polynomial.C 1) (fun p => firstBit p.2) (fun _ => true) := by
  intro h
  have hx : (2 / 3 : ℚ) ≤ probability 1 firstBit := by simpa using h []
  rw [firstBit_probability] at hx
  norm_num at hx

example : OneSidedError (Polynomial.C 1) (fun p => firstBit p.2) (fun _ => true) := by
  intro x
  constructor
  · intro _
    simpa using (show (1 / 2 : ℚ) ≤ probability 1 firstBit by
      rw [firstBit_probability])
  · intro h
    cases h

/-- A false positive on just one possible coin string already violates RP correctness. -/
theorem rejects_false_positives :
    ¬ OneSidedError (Polynomial.C 1) (fun p => firstBit p.2) (fun _ => false) := by
  intro h
  have hx := (h []).2 rfl [true] (by simp)
  change true = false at hx
  cases hx

example : BoundedError 0 (fun _ => false) (fun _ => false) := by
  intro x
  simp only [Polynomial.eval_zero]
  change (2 / 3 : ℚ) ≤ probability 0 (fun _ => true)
  rw [probability_true]
  norm_num

example : ¬ BoundedError 0 (fun _ => true) (fun _ => false) := by
  intro h
  have hx := h []
  simp only [Polynomial.eval_zero] at hx
  change (2 / 3 : ℚ) ≤ probability 0 (fun _ => false) at hx
  rw [probability_false] at hx
  norm_num at hx

example : ¬ BoundedError 0 (fun _ => false) firstBit := by
  intro h
  have hx := h [true]
  simp only [Polynomial.eval_zero] at hx
  change (2 / 3 : ℚ) ≤ probability 0 (fun _ => false) at hx
  rw [probability_false] at hx
  norm_num at hx

example : (fun _ => true) ∈ ZPP ↔
    (fun _ => true) ∈ RP ∧ (fun _ => false) ∈ RP := Iff.rfl

def orCircuit : Circuit (Fin 2) :=
  .step (.or (.inl 0) (.inl 1)) (.output (.inr 0))

def projection : Circuit (Fin 2) := .output (.inl 0)

example : orCircuit.size = 1 := rfl
example : orCircuit.neg.size = 1 := rfl
example : projection.size = 0 := rfl
example : circuitTest orCircuit [false, true] = true := rfl
example : circuitTest orCircuit [false, false] = false := rfl
theorem orCircuit_probability : probability 2 (circuitTest orCircuit) = 3 / 4 := by
  norm_num [probability, show count 2 (circuitTest orCircuit) = 3 by decide]

theorem projection_probability : probability 2 (circuitTest projection) = 1 / 2 := by
  norm_num [probability, show count 2 (circuitTest projection) = 2 by decide]

example : ¬ IsPRG 2 2 2 (1 / 8) id := fun h => Nat.lt_irrefl 2 h.1
example : ¬ IsPRG 0 0 0 (1 / 8) id := not_isPRG_zero_output 0 0 (1 / 8) id

/-- Duplicating a uniform bit fools projections but fails a one-gate OR test. -/
theorem repeated_bit_is_not_prg :
    ¬ IsPRG 1 2 2 (1 / 8) (fun r => r ++ r) := by
  intro h
  have hx := h.2.2 orCircuit (by decide)
  rw [orCircuit_probability] at hx
  norm_num [probability,
    show count 1 (fun r => circuitTest orCircuit (r ++ r)) = 1 by decide] at hx

example : ¬ IsPRG 0 2 2 (1 / 8) (fun _ => [false, false]) := by
  intro h
  have hx := h.2.2 projection (by decide)
  rw [projection_probability] at hx
  norm_num [probability,
    show count 0 (fun _ => circuitTest projection [false, false]) = 0 by decide] at hx

example : ¬ IsPRG 1 2 2 (1 / 8) (fun _ => [true]) := by
  intro h
  have hx := h.2.1 [false] rfl
  cases hx

example : (BitstringEncoding.bitEncode (BooleanTruthTable.UnarySize.mk 12)).length = 12 := by
  decide
example : BitstringEncoding.bitDecode (α := BooleanTruthTable.UnarySize) [true, false] = none := by
  decide

def oneEdge : Code := [[false, true], [true, false]]
def noEdges : Code := [[false, false], [false, false]]

example : ValidColoredGraph oneEdge oneEdge := by decide
example : ValidColoredGraph oneEdge noEdges := by decide
example : ¬ ValidColoredGraph noEdges oneEdge := by decide
example : ¬ ValidColoredGraph oneEdge [] := by decide
example : ¬ ValidColoredGraph [[true]] [[false]] := by decide
example : ¬ ValidColoredGraph [[false, true], [false, false]] noEdges := by decide
example : ¬ ValidColoredGraph [[false], [false]] noEdges := by decide
example : ¬ ValidColoredGraph oneEdge [[false, true], [false, false]] := by decide

example : ExactMatching ([], [], 0) := by decide
example : ¬ ExactMatching ([], [], 1) := by decide
example : ¬ ExactMatching ([], [], -1) := by decide
example : ¬ ExactMatching ([[false]], [[false]], 0) := by decide
example : ExactMatching (oneEdge, oneEdge, 1) := by decide
example : ¬ ExactMatching (oneEdge, oneEdge, 0) := by decide
example : ¬ ExactMatching (oneEdge, oneEdge, 2) := by decide
example : ExactMatching (oneEdge, noEdges, 0) := by decide
example : ¬ ExactMatching (oneEdge, noEdges, 1) := by decide
example : ¬ ExactMatching (noEdges, noEdges, 0) := by decide
example : ¬ ExactMatching (oneEdge, oneEdge, -1) := by decide

def cycleFour : Code :=
  [[false, true, false, true], [true, false, true, false],
   [false, true, false, true], [true, false, true, false]]

def oppositeRed : Code :=
  [[false, true, false, false], [true, false, false, false],
   [false, false, false, true], [false, false, true, false]]

example : ExactMatching (cycleFour, oppositeRed, 0) := by
  refine ⟨by decide, fun i => ⟨3 - i.val, by change 3 - i.val < 4; omega⟩, ?_, ?_⟩ <;> decide
example : ExactMatching (cycleFour, oppositeRed, 2) := by decide

/-- Exact Matching is not a minimum/maximum interval test: attainable counts can have gaps. -/
theorem red_count_gap : ¬ ExactMatching (cycleFour, oppositeRed, 1) := by
  have h : ∀ a b c d : Fin 4,
      let mate := Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Fin.elim0)))
      ¬ (IsMate cycleFour mate ∧ (redCount cycleFour oppositeRed mate : ℤ) = 1) := by
    intro a b c d
    dsimp only
    unfold IsMate Function.Involutive
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
  rintro ⟨_, mate, hm, hk⟩
  change Fin 4 → Fin 4 at mate
  have heq : mate =
      Fin.cons (mate 0) (Fin.cons (mate 1) (Fin.cons (mate 2) (Fin.cons (mate 3) Fin.elim0))) := by
    funext i
    fin_cases i <;> rfl
  exact h (mate 0) (mate 1) (mate 2) (mate 3) (heq ▸ ⟨hm, hk⟩)

def triangle : Code :=
  [[false, true, true], [true, false, true], [true, true, false]]

example : ¬ ExactMatching (triangle, triangle, 0) := by decide
example : ¬ ExactMatching (triangle, triangle, 1) := by decide
example : ¬ ExactMatching (triangle, triangle, 2) := by decide

def completeFour : Code :=
  [[false, true, true, true], [true, false, true, true],
   [true, true, false, true], [true, true, true, false]]

example : ExactMatching (completeFour, completeFour, 2) := by
  refine ⟨by decide,
    (Fin.cons 1 (Fin.cons 0 (Fin.cons 3 (Fin.cons 2 Fin.elim0))) : Fin 4 → Fin 4),
    ?_, ?_⟩
  · constructor <;> intro i <;> change Fin 4 at i <;> fin_cases i <;> rfl
  · decide

example (a red : Code) (k : ℤ) (h : ExactMatching (a, red, k)) : Even a.length :=
  h.even_vertices
example (a red : Code) (k : ℤ) (h : ExactMatching (a, red, k)) : 0 ≤ k :=
  h.nonneg_target

#guard probability 4 firstBit == (1 / 2 : ℚ)
#guard decide (ExactMatching (cycleFour, oppositeRed, 2))
#guard !decide (ExactMatching (cycleFour, oppositeRed, 1))

end RandomizationTest
