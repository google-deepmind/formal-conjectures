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

public import FormalConjecturesForMathlib.GameTheory.StochasticGame.Equilibrium

/-!
# Approximate subgame perfection in finite stochastic games

Every continuation starts a fresh trajectory at the full feasible history, including histories
that have zero probability under the profile. Only the payoff horizon restarts. The original
strategy kernels retain the recorded history, and unilateral deviations are unrestricted.

These predicates express the refinements in Econ-1(d),
https://we-solve.github.io/problems/equilibrium-payoffs-in-finite-multiplayer-stochastic-games/.
They impose no continuation payoff target. In the uniform version the horizon threshold may
depend on the history; no threshold uniform over all histories is required.
-/

@[expose] public section

open Filter
open scoped Topology

namespace StochasticGame.Game

variable {I S : Type} [Fintype I] [Fintype S]
variable (G : StochasticGame.Game I S)

/-- Approximate Nash incentives for all long enough horizons after each feasible history.
The positive horizon threshold is chosen separately for each history. -/
def SubgameUniform (σ : G.Profile) (ε : ℝ) : Prop :=
  ∀ h : G.History, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (i : I) (τ : G.Strategy i),
      G.expectedAverageFrom h (G.revise σ i τ) i N ≤ G.expectedAverageFrom h σ i N + ε

/-- Approximate Nash incentives after every feasible history for one lower-limit evaluation. -/
def SubgameLongRun (evaluation : LongRunEvaluation) (σ : G.Profile) (ε : ℝ) : Prop :=
  ∀ (h : G.History) (i : I) (τ : G.Strategy i),
    G.longRunPayoffFrom evaluation h (G.revise σ i τ) i ≤
      G.longRunPayoffFrom evaluation h σ i + ε

/-- Own continuation averages converge, and all deviation upper limits satisfy Nash incentives. -/
def SubgameMean (σ : G.Profile) (ε : ℝ) : Prop :=
  ∀ (h : G.History) (i : I), ∃ L : ℝ,
    Tendsto (fun N ↦ G.expectedAverageFrom h σ i N) atTop (𝓝 L) ∧
      ∀ τ : G.Strategy i, G.limsupExpectedFrom h (G.revise σ i τ) i ≤ L + ε

theorem SubgameUniform.mono {σ : G.Profile} {ε δ : ℝ}
    (h : G.SubgameUniform σ ε) (hεδ : ε ≤ δ) : G.SubgameUniform σ δ := by
  intro history
  obtain ⟨N₀, hN₀, hw⟩ := h history
  exact ⟨N₀, hN₀, fun N hN i τ ↦ (hw N hN i τ).trans (by linarith)⟩

theorem SubgameLongRun.mono {evaluation : LongRunEvaluation} {σ : G.Profile} {ε δ : ℝ}
    (h : G.SubgameLongRun evaluation σ ε) (hεδ : ε ≤ δ) :
    G.SubgameLongRun evaluation σ δ := by
  intro history i τ
  exact (h history i τ).trans (by linarith)

theorem SubgameMean.mono {σ : G.Profile} {ε δ : ℝ}
    (h : G.SubgameMean σ ε) (hεδ : ε ≤ δ) : G.SubgameMean σ δ := by
  intro history i
  obtain ⟨L, hL, hw⟩ := h history i
  exact ⟨L, hL, fun τ ↦ (hw τ).trans (by linarith)⟩

/-- The initial-state incentive inequalities are among the lower-limit subgame inequalities. -/
theorem SubgameLongRun.initial {evaluation : LongRunEvaluation} {σ : G.Profile} {ε : ℝ}
    (h : G.SubgameLongRun evaluation σ ε) (s : S) (i : I) (τ : G.Strategy i) :
    G.longRunPayoff evaluation s (G.revise σ i τ) i ≤
      G.longRunPayoff evaluation s σ i + ε :=
  h (History.initial s) i τ

/-- Constant rewards satisfy the uniform continuation requirement, with threshold one at each
history, regardless of the profile or its support. -/
theorem subgameUniform_of_constant_reward (σ : G.Profile) (c : I → ℝ)
    (hc : ∀ i s a, G.reward i s a = c i) {ε : ℝ} (hε : 0 ≤ ε) :
    G.SubgameUniform σ ε := by
  intro history
  refine ⟨1, le_rfl, fun N hN i τ ↦ ?_⟩
  rw [G.expectedAverageFrom_of_constant_reward i (c i) (hc i) history
      (G.revise σ i τ) (by omega),
    G.expectedAverageFrom_of_constant_reward i (c i) (hc i) history σ (by omega)]
  linarith

end StochasticGame.Game
