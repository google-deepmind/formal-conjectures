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

public import FormalConjecturesForMathlib.GameTheory.StochasticGame.Basic
public import FormalConjecturesForMathlib.Probability.BoundedPayoffs

/-!
# Payoffs of actual stochastic-game play

Evaluate the bounded rewards against the game's constructed trajectory law. Starting at a full
history restarts averaging but retains all recorded information in the strategy kernels.
Pathwise lower limits and lower limits of expected averages are distinct evaluations.

References: Solan–Vieille, *Stochastic games* (2015),
https://pmc.ncbi.nlm.nih.gov/articles/PMC4653174/; the long-run evaluation conventions in
https://we-solve.github.io/problems/equilibrium-payoffs-in-finite-multiplayer-stochastic-games/.
-/

@[expose] public section

namespace StochasticGame

/-- The two distinct lower-limit evaluations; no interchange of expectation and liminf. -/
inductive LongRunEvaluation
  | pathLiminf
  | expectedLiminf

namespace Game

variable {I S : Type} [Fintype I] [Fintype S]
variable (G : Game I S)

/-- The reward process along an actual public-turn trajectory. -/
noncomputable def rewardProcess (i : I) : BoundedPayoffs.Process (ℕ → G.Turn) where
  reward t ω := G.stageReward i (ω t)
  measurable_reward t := (G.measurable_stageReward i).comp (measurable_pi_apply t)
  bound := G.rewardBound
  bound_nonneg := G.rewardBound_nonneg
  norm_reward_le t ω := G.norm_stageReward_le i (ω t)

/-- Expected average of the next `N` stages from a complete history. -/
noncomputable def expectedAverageFrom (h : G.History) (σ : G.Profile) (i : I) (N : ℕ) : ℝ :=
  (G.rewardProcess i).expectedAverage (G.lawFrom h σ) N

/-- Expected average from an initial public state; all research questions use `N ≥ 1`. -/
noncomputable def expectedAverage (s : S) (σ : G.Profile) (i : I) (N : ℕ) : ℝ :=
  G.expectedAverageFrom (History.initial s) σ i N

/-- Expected discounted continuation payoff, with rate tending to zero for patient play. -/
noncomputable def expectedDiscountedFrom (h : G.History) (σ : G.Profile) (i : I)
    (rate : ℝ) : ℝ :=
  (G.rewardProcess i).expectedDiscounted (G.lawFrom h σ) rate

/-- Expected normalized discounted payoff from an initial state. -/
noncomputable def expectedDiscounted (s : S) (σ : G.Profile) (i : I) (rate : ℝ) : ℝ :=
  G.expectedDiscountedFrom (History.initial s) σ i rate

/-- Expectation of the pathwise lower limit of continuation averages. -/
noncomputable def expectedPathLiminfFrom (h : G.History) (σ : G.Profile) (i : I) : ℝ :=
  (G.rewardProcess i).expectedPathLiminf (G.lawFrom h σ)

/-- Lower limit of expected continuation averages. -/
noncomputable def liminfExpectedFrom (h : G.History) (σ : G.Profile) (i : I) : ℝ :=
  (G.rewardProcess i).liminfExpected (G.lawFrom h σ)

/-- Upper limit of expected continuation averages, also used for nonconvergent deviations. -/
noncomputable def limsupExpectedFrom (h : G.History) (σ : G.Profile) (i : I) : ℝ :=
  (G.rewardProcess i).limsupExpected (G.lawFrom h σ)

/-- One of the two explicitly selected lower-limit continuation evaluations. -/
noncomputable def longRunPayoffFrom (evaluation : LongRunEvaluation) (h : G.History)
    (σ : G.Profile) (i : I) : ℝ :=
  match evaluation with
  | .pathLiminf => G.expectedPathLiminfFrom h σ i
  | .expectedLiminf => G.liminfExpectedFrom h σ i

/-- A selected lower-limit payoff from an initial state. -/
noncomputable def longRunPayoff (evaluation : LongRunEvaluation) (s : S)
    (σ : G.Profile) (i : I) : ℝ :=
  G.longRunPayoffFrom evaluation (History.initial s) σ i

/-- Upper limiting expected average from an initial state. -/
noncomputable def limsupExpected (s : S) (σ : G.Profile) (i : I) : ℝ :=
  G.limsupExpectedFrom (History.initial s) σ i

theorem norm_expectedAverageFrom_le (h : G.History) (σ : G.Profile) (i : I) (N : ℕ) :
    ‖G.expectedAverageFrom h σ i N‖ ≤ G.rewardBound :=
  (G.rewardProcess i).norm_expectedAverage_le _ _

theorem norm_expectedAverage_le (s : S) (σ : G.Profile) (i : I) (N : ℕ) :
    ‖G.expectedAverage s σ i N‖ ≤ G.rewardBound :=
  G.norm_expectedAverageFrom_le _ _ _ _

theorem norm_expectedPathLiminfFrom_le (h : G.History) (σ : G.Profile) (i : I) :
    ‖G.expectedPathLiminfFrom h σ i‖ ≤ G.rewardBound :=
  (G.rewardProcess i).norm_expectedPathLiminf_le _

theorem norm_longRunPayoffFrom_le (evaluation : LongRunEvaluation) (h : G.History)
    (σ : G.Profile) (i : I) : ‖G.longRunPayoffFrom evaluation h σ i‖ ≤ G.rewardBound := by
  cases evaluation
  · exact G.norm_expectedPathLiminfFrom_le h σ i
  · exact (G.rewardProcess i).norm_liminfExpected_le _

theorem norm_longRunPayoff_le (evaluation : LongRunEvaluation) (s : S)
    (σ : G.Profile) (i : I) : ‖G.longRunPayoff evaluation s σ i‖ ≤ G.rewardBound :=
  G.norm_longRunPayoffFrom_le _ _ _ _

/-- Constant stage rewards give the same average from any history, including profile-null ones. -/
theorem expectedAverageFrom_of_constant_reward (i : I) (c : ℝ)
    (hc : ∀ s a, G.reward i s a = c) (h : G.History) (σ : G.Profile)
    {N : ℕ} (hN : 0 < N) : G.expectedAverageFrom h σ i N = c := by
  have havg (ω : ℕ → G.Turn) : (G.rewardProcess i).average N ω = c := by
    change (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N,
      G.reward i (ω t).1.current (ω t).2 = c
    simp_rw [hc]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    field_simp
  unfold expectedAverageFrom BoundedPayoffs.Process.expectedAverage
  simp_rw [havg]
  simp

end Game
end StochasticGame
