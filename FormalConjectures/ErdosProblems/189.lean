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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 189

*Reference:* [erdosproblems.com/189](https://www.erdosproblems.com/189)
-/

open Affine EuclideanGeometry

namespace Erdos189

/-- Erdős problem 189 asked whether the below holds for all rectangles. -/
def Erdos189For (P : ℝ² → ℝ² → ℝ² → ℝ² → Prop) (A : ℝ² → ℝ² → ℝ² → ℝ² → ℝ) :=
    ∀ᵉ (n > 0) (colouring : ℝ² → Fin n), ∃ colour, ∀ area > (0 : ℝ), ∃ a b c d,
      {a, b, c, d} ⊆ colouring⁻¹' {colour} ∧
      IsCcwConvexPolygon ![a, b, c, d] ∧
      A a b c d = area ∧
      P a b c d

/--
If $\mathbb{R}^2$ is finitely coloured then must there exist some colour class which contains the
vertices of a rectangle of every area?

Graham, "On Partitions of 𝔼ⁿ", Journal of Combinatorial Theory, Series A 28, 89-91 (1980).
(See "Concluding Remarks" on page 96.)

Solved (with answer `False`, as formalised below) in:
Vjekoslav Kovač, "Coloring and density theorems for configurations of a given volume", 2023
https://arxiv.org/abs/2309.09973
In fact, Kovač's colouring is even Jordan measurable (the topological boundary of each
monochromatic region is Lebesgue measurable and has measure zero).

This was formalized in Lean by Alexeev and Kovac using Aristotle.
-/
@[category research formally solved using lean4 at
"https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos189.lean", AMS 5 51]
theorem erdos_189 :
    answer(False) ↔ Erdos189For
      (fun a b c d ↦
        line[ℝ, a, b].direction ⟂ line[ℝ, b, c].direction ∧
        line[ℝ, b, c].direction ⟂ line[ℝ, c, d].direction ∧
        line[ℝ, c, d].direction ⟂ line[ℝ, d, a].direction)
      (fun a b c d ↦ dist a b * dist b c) := by
  sorry

/-- Graham claims this is "easy to see". -/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/189.lean", AMS 5 51]
theorem erdos_189.variants.square :
    ¬ Erdos189For
      (fun a b c d ↦
        line[ℝ, a, b].direction ⟂ line[ℝ, b, c].direction ∧
        line[ℝ, b, c].direction ⟂ line[ℝ, c, d].direction ∧
        line[ℝ, c, d].direction ⟂ line[ℝ, d, a].direction ∧
        dist a b = dist b c)
      (fun a b c d ↦ dist a b * dist b c) := by
  sorry

/--
Seems to be open, as of January 2025.
-/
@[category research open, AMS 5 51]
theorem erdos_189.variants.parallelogram :
    ¬ Erdos189For
      (fun a b c d ↦
        line[ℝ, a, b] ∥ line[ℝ, c, d] ∧
        line[ℝ, a, d] ∥ line[ℝ, b, c])
      (fun a b c d ↦ dist a b * dist b c * (∡ a b c).sin) := by
  sorry

end Erdos189
