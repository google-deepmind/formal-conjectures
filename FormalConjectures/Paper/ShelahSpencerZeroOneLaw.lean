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

import FormalConjecturesUtil

/-! # Shelah-Spencer's Zero-One Law for Sparse Random Graphs

*References*:

* [Shelah and Spencer,
  Zero-one laws for sparse random graphs](https://doi.org/10.1090/S0894-0347-1988-0924703-8),
  Journal of the American Mathematical Society, 1(1), 97-115 (1988).
* [Glebskii et al.,
  Range and degree of realizability of formulas
  in the restricted predicate calculus](https://doi.org/10.1007/BF01071084),
  Cybernetics, 5(2), 142-154 (1969) (for $\alpha = 0$).
-/

open FirstOrder Filter MeasureTheory Topology
namespace ShelahSpencerZeroOneLaw

/-- The edge probability $n^{-\alpha}$ as an element of the unit interval.

At $n = 0$, this uses Mathlib's convention $0^{-\alpha} = 0$. This choice does not affect an
asymptotic statement as $n \to \infty$. -/
noncomputable def sparseProbability (n : ℕ) (α : ℝ) (hα : 0 < α) : unitInterval :=
  ⟨(n : ℝ) ^ (-α), Real.rpow_nonneg (Nat.cast_nonneg n) (-α), by
    cases n with
    | zero => simpa using Real.zero_rpow_le_one (-α)
    | succ n =>
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (by simp [hα.le])⟩

/-- The probability law $G(n, n^{-\alpha})$ on simple graphs with vertex set `Fin n`. -/
noncomputable def sparseRandomGraph (n : ℕ) (α : ℝ) (hα : 0 < α) :
    Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) (sparseProbability n α hα)

/-- If $0 < \alpha < 1$ is irrational, then for every first-order sentence $\varphi$ in the
language of graphs, the probability that $G(n, n^{-\alpha})$ satisfies $\varphi$ tends to either
zero or one as $n \to \infty$. -/
@[category research solved, AMS 3 5]
theorem zeroOne_irrational
  (α : ℝ) (hα : 0 < α ∧ α < 1) (hirr : Irrational α) (φ : Language.graph.Sentence) :
   Tendsto (fun n =>
     sparseRandomGraph n α hα.1
       {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}) atTop (𝓝 0) ∨
   Tendsto (fun n =>
     sparseRandomGraph n α hα.1
       {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}) atTop (𝓝 1) := by
  sorry

/-- If $0 < \alpha < 1$ is rational, then there is a first-order sentence $\varphi$ in the
language of graphs whose probability in $G(n, n^{-\alpha})$ does not converge as
$n \to \infty$. -/
@[category research solved, AMS 3 5]
theorem zeroOne_rational
  (α : ℝ) (hα : 0 < α ∧ α < 1) (hrat : ¬Irrational α) :
   ∃ φ : Language.graph.Sentence,
   ∀ b : ENNReal,
   ¬ Tendsto (fun n =>
     sparseRandomGraph n α hα.1
       {G | @Language.Sentence.Realize Language.graph (Fin n) G.structure φ}) atTop (𝓝 b) := by
  sorry
end ShelahSpencerZeroOneLaw
