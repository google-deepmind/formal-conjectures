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
# Pointwise convergence for two commuting transformations

Problem 19 in Section 5.2.5 of Frantzikinakis's survey [Fr16]. The problem asks
for almost-everywhere convergence of bilinear averages of bounded functions
under two commuting invertible measure-preserving transformations.
Kenta Kitamura's Lean formalization [Ki26] gives an affirmative answer and
extends the conclusion to square-integrable inputs.

Both statements concern an arbitrary probability space and each fixed pair
of inputs; no ergodicity is assumed. We use sums over $n = 0, \ldots, N-1$.
The sums over $n = 1, \ldots, N$ in [Fr16] have the same limit [Ki26].

*References:*
- [Fr16] Nikos Frantzikinakis, *Some open problems on multiple ergodic averages*,
  [arXiv:1103.3808v3](https://arxiv.org/abs/1103.3808v3) (2016),
  [Section 5.2.5, Problem 19](https://arxiv.org/html/1103.3808v3#S5.SS2.SSS5).
- [Ki26] Kenta Kitamura, *commuting-pointwise-convergence*,
  Lean 4 formalization (2026),
  [complete target proofs](https://github.com/KitaKen1/commuting-pointwise-convergence/blob/a7fe00845b28bf2df2a4e2ec84fe0e13ba44fe6d/lean/verification/FCTargetProofs.lean).
-/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace CommutingConvergence

/-- Problem 19 in [Fr16, Section 5.2.5]: do the bilinear averages of every pair
of bounded functions converge almost everywhere for two commuting invertible
measure-preserving transformations? The answer is affirmative [Ki26].
Invertibility includes measurability of the inverse; no ergodicity is assumed. -/
@[category research solved, AMS 28 37,
    formal_proof using lean4 at "https://github.com/KitaKen1/commuting-pointwise-convergence/blob/a7fe00845b28bf2df2a4e2ec84fe0e13ba44fe6d/lean/verification/FCTargetProofs.lean"]
theorem commutingPointwiseConvergence :
    answer(True) ↔
      ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
        (T S : X ≃ᵐ X),
        MeasurePreserving T μ μ → MeasurePreserving S μ μ →
        Function.Commute (T : X → X) (S : X → X) →
        ∀ (f g : X → ℂ), MemLp f ∞ μ → MemLp g ∞ μ →
          ∀ᵐ x ∂μ, ∃ L : ℂ,
            Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ *
              ∑ n ∈ Finset.range N, f (T^[n] x) * g (S^[n] x)) atTop (𝓝 L) := by
  sorry

/-- The square-integrable extension of [Fr16, Section 5.2.5, Problem 19]:
do the same bilinear averages converge almost everywhere for every pair of
$L^2$ functions? The answer is affirmative [Ki26]. -/
@[category research solved, AMS 28 37,
    formal_proof using lean4 at "https://github.com/KitaKen1/commuting-pointwise-convergence/blob/a7fe00845b28bf2df2a4e2ec84fe0e13ba44fe6d/lean/verification/FCTargetProofs.lean"]
theorem commutingPointwiseConvergenceL2 :
    answer(True) ↔
      ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
        (T S : X ≃ᵐ X),
        MeasurePreserving T μ μ → MeasurePreserving S μ μ →
        Function.Commute (T : X → X) (S : X → X) →
        ∀ (f g : X → ℂ), MemLp f 2 μ → MemLp g 2 μ →
          ∀ᵐ x ∂μ, ∃ L : ℂ,
            Tendsto (fun N : ℕ ↦ (N : ℂ)⁻¹ *
              ∑ n ∈ Finset.range N, f (T^[n] x) * g (S^[n] x)) atTop (𝓝 L) := by
  sorry

end CommutingConvergence
