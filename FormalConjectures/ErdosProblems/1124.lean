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
# Erdős Problem 1124

*References:*
- [erdosproblems.com/1124](https://www.erdosproblems.com/1124)
- [Er81b] Erdős, P., *My Scottish Book 'Problems'*. The Scottish Book (1981), 27-35.
- [La90b] Laczkovich, M., *Equidecomposability and discrepancy; a solution of Tarski's
  circle-squaring problem*. J. Reine Angew. Math. (1990), 77-117.
-/

@[expose] public section

open Metric Real

namespace Erdos1124

/-- The Euclidean plane. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The closed axis-parallel square centred at the origin with side length `s`. -/
def square (s : ℝ) : Set ℝ² := {x | ∀ i, |x i| ≤ s / 2}

/--
Can a square and a circle of the same area be decomposed into a finite number of congruent parts?

A problem of Tarski, which Erdős described as 'a very beautiful problem...if it were my problem I
would offer \$1000 for it'.

This is true - Laczkovich [La90b] proved that in fact this is possible using translations only.

Equidecomposability is expressed with Mathlib's `Equidecomp`: a bijection between the two sets
which, on each of finitely many pieces, is given by a single isometry of the plane.
-/
@[category research solved, AMS 28 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1124.lean#L236"]
theorem erdos_1124 : answer(True) ↔ ∀ r : ℝ, 0 < r →
    ∃ e : Equidecomp ℝ² (ℝ² ≃ᵢ ℝ²), e.source = closedBall 0 r ∧
      e.target = square (√π * r) := by
  sorry

/-- Laczkovich [La90b] proved that the decomposition is possible using translations only. -/
@[category research solved, AMS 28 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1124.lean#L236"]
theorem erdos_1124.variants.translations : ∀ r : ℝ, 0 < r →
    ∃ e : Equidecomp ℝ² (Multiplicative ℝ²), e.source = closedBall 0 r ∧
      e.target = square (√π * r) := by
  sorry

end Erdos1124
