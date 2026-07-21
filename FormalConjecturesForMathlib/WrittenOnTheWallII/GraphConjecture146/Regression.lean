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
public import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.ExceptionalTheorem

@[expose] public section

/-!
# Regression witness for the exceptional radius-2 case

The hypotheses of `WrittenOnTheWallII.GraphConjecture146.Proof.exceptional_case` are nonvacuous. This module adapts
Claude's independent regression witness: the six-vertex spider consisting of
path `0-1-2-3-4` plus pendant edge `2-5`.
-/

open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture146.Proof.Regression

/-- Edge relation of the witness graph: path `0-1-2-3-4` plus pendant `2-5`. -/
def regRel : Fin 6 → Fin 6 → Prop := fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨
    (a = 3 ∧ b = 4) ∨ (a = 2 ∧ b = 5)

instance : DecidableRel regRel := fun a b => by
  unfold regRel
  infer_instance

/-- The witness graph on `Fin 6`. -/
def regGraph : SimpleGraph (Fin 6) := SimpleGraph.fromRel regRel

instance : DecidableRel regGraph.Adj :=
  fun a b => decidable_of_iff _ (SimpleGraph.fromRel_adj regRel a b).symm

theorem reg_connected : regGraph.Connected := by decide

set_option maxRecDepth 4000 in
theorem reg_radius : regGraph.radius.toNat = 2 := by
  rw [radius_eq_computable regGraph reg_connected, ENat.toNat_coe]
  decide

set_option maxRecDepth 4000 in
theorem reg_diam : regGraph.diam = 4 := by
  show regGraph.ediam.toNat = 4
  rw [ediam_eq_computable regGraph reg_connected, ENat.toNat_coe]
  decide

set_option maxRecDepth 8000 in
theorem reg_periphery :
    regGraph.maxEccentricityVertices = ({0, 4} : Set (Fin 6)) := by
  ext v
  rw [SimpleGraph.maxEccentricityVertices, Set.mem_setOf_eq,
    eccent_eq_computable regGraph reg_connected,
    ediam_eq_computable regGraph reg_connected, Nat.cast_inj]
  fin_cases v <;> decide

set_option maxRecDepth 8000 in
theorem reg_eccSet :
    regGraph.eccSet regGraph.maxEccentricityVertices = 3 := by
  rw [reg_periphery]
  simp only [SimpleGraph.eccSet, SimpleGraph.distToSet, dist_eq_computable,
    Set.toFinset_insert, Set.toFinset_singleton]
  decide

/-- The concrete graph satisfies the exceptional hypotheses, proving the
exceptional theorem is not vacuous. -/
theorem reg_exceptional : 6 ≤ regGraph.largestInducedTreeSize :=
  WrittenOnTheWallII.GraphConjecture146.Proof.exceptional_case regGraph reg_connected reg_radius reg_diam reg_eccSet


end WrittenOnTheWallII.GraphConjecture146.Proof.Regression
