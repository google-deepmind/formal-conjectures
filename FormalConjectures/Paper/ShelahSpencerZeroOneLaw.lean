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

import FormalConjectures.ForMathlib.Probability.ShelahSpencer
import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Real.Irrational
import Mathlib.ModelTheory.Graph

/-! # Shelah-Spencer's Zero-One Law for Sparse Random Graphs

*Reference*: [Zero-one laws for sparse random graphs]
Journal of the American Mathematical Society, 1(1), 97-115.
by *S. Shelah* and *J. Spencer*

[Range and degree of realizability of formulas in the restricted predicate calculus]
Cybernetics, 5(2), 142-154.
by *Glebskii, Y. V., Kogan, D. I., Liogon'kiI, M. I., & Talanov, V. A. (1969)* (for α = 0)
-/

open ShelahSpencer FirstOrder Filter Topology
namespace ShelahSpencerZeroOneLaw

/--
`[1] ∀ α ∈ (0, 1) ∖ ℚ, ∀ ψ ∈ T, limₙ μ({G: G ∈ SimpleGraph(Fin(n)) ⊨ ψ}) exists and is 1 or 0`
     where `T` is the set of all Sentences in the language of graphs, `μ` is
     `ShelahSpencer.Measure n α` as defined in Probability.Basic.
-/
@[category research solved, AMS 03 05]
theorem zeroOne_irrational
  (α : ℝ)(hα : 0 < α ∧ α < 1) (hirr : Irrational α) (φ : Language.graph.Sentence) :
   Tendsto (fun n =>
     (ShelahSpencer.Measure' (E := Fin n) α) {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure
       φ}) atTop (𝓝 0) ∨
   Tendsto (fun n =>
     (ShelahSpencer.Measure' (E := Fin n) α) {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure
       φ}) atTop (𝓝 1) := by sorry

/-- `[2] ∀ α ∈ (0, 1) ∩ ℚ, ∃ ψ ∈ T, limₙ μ({G: G ∈ SimpleGraph(Fin(n)) ⊨ ψ}) does not exist.`
(Theorem 2 gives "oscillation")
-/
@[category research solved, AMS 03 05]
theorem zeroOne_rational
  (α : ℝ)(hα : 0 < α ∧ α < 1) (hrat : ¬Irrational α) :
   ∃ φ : Language.graph.Sentence,
   ∀ b : ENNReal,
   ¬ Tendsto (fun n =>
     (ShelahSpencer.Measure' (E := Fin n) α) {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure
       φ}) atTop (𝓝 b) := by sorry
end ShelahSpencerZeroOneLaw
