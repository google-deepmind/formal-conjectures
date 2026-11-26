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

public import FormalConjecturesUtil

/-!
# Erdős Problem 527

*References:*
- [erdosproblems.com/527](https://www.erdosproblems.com/527)
- [MiSa25] M. Michelen and M. Sawhney, _Convergent points for random power series
  on the unit circle_. arXiv:2509.02729 (2025). https://arxiv.org/abs/2509.02729
- The probability model and convergence predicates follow the Apache 2.0 formalization at
  https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos527.lean
-/

@[expose] public section

open Asymptotics Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos527

/-- The parameter of a fair Bernoulli law. -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num⟩

/-- The fair sign law on the real numbers. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure (1 : ℝ) (-1 : ℝ) half

instance : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- One infinite sequence of independent fair signs. -/
noncomputable def rademacherProductMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure

instance : IsProbabilityMeasure rademacherProductMeasure := by
  unfold rademacherProductMeasure
  infer_instance

/-- A term of the signed power series. -/
def seriesTerm (a ε : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ((ε n * a n : ℝ) : ℂ) * z ^ n

/-- Convergence of the series in its natural order, allowing conditional convergence. -/
def SeriesConvergesAt (a ε : ℕ → ℝ) (z : ℂ) : Prop :=
  Summable (seriesTerm a ε z) (SummationFilter.conditional ℕ)

/-- The sum of squared absolute coefficients diverges to infinity. -/
def SquareSumDiverges (a : ℕ → ℝ) : Prop :=
  Tendsto (fun N ↦ ∑ n ∈ Finset.range N, |a n| ^ 2) atTop atTop

/-- The coefficients have size $o(1/\sqrt{n})$. -/
def DecaysFasterThanInvSqrt (a : ℕ → ℝ) : Prop :=
  (fun n : ℕ ↦ |a n|) =o[atTop] (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹)

/--
Let $a_n\in \mathbb{R}$ be such that $\sum_n \lvert a_n\rvert^2=\infty$ and $\lvert
a_n\rvert=o(1/\sqrt{n})$. Is it true that, for almost all $\epsilon_n=\pm 1$, there exists some
$z$ with $\lvert z\rvert=1$ (depending on the choice of signs) such that$$\sum_n \epsilon_n a_n
z^n$$converges?

This is true, and was proved by Michelen and Sawhney [MiSa25], who in fact proved
that the set of such $z$ has Hausdorff dimension $1$.
-/
@[category research solved, AMS 30 60, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos527.lean"]
theorem erdos_527 : answer(True) ↔ ∀ a : ℕ → ℝ,
    SquareSumDiverges a → DecaysFasterThanInvSqrt a →
      ∀ᵐ ε ∂rademacherProductMeasure,
        ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z := by
  sorry

end Erdos527
