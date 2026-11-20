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

public import FormalConjecturesForMathlib.GameTheory.StochasticGame.Payoffs

/-!
# Approximate equilibrium payoffs in finite stochastic games

The predicates keep the payoff vector outside the error tolerance, and use one profile for every
initial state. `admissible ε σ` restricts witnessing profiles; deviations always range over all
behavioral strategies.

References: Neyman, *Robust Optimization in Stochastic Games*, §3.6,
https://arxiv.org/abs/2611.01151; the distinct long-run conventions in
https://we-solve.github.io/problems/equilibrium-payoffs-in-finite-multiplayer-stochastic-games/.
-/

@[expose] public section

open Filter
open scoped Topology

namespace StochasticGame.Game

variable {I S : Type} [Fintype I] [Fintype S]
variable (G : StochasticGame.Game I S)

/-- One profile approximates `v` and is Nash for every sufficiently large positive horizon.
The threshold is common to all initial states and all unilateral deviations. -/
def UniformWitness (σ : G.Profile) (v : I → S → ℝ) (ε : ℝ) : Prop :=
  ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ (s : S) (i : I) (N : ℕ), N₀ ≤ N →
    |G.expectedAverage s σ i N - v i s| ≤ ε ∧
      ∀ τ : G.Strategy i,
        G.expectedAverage s (G.revise σ i τ) i N ≤ G.expectedAverage s σ i N + ε

/-- Uniform approximate equilibrium payoffs with a specified class of witnessing profiles. -/
def HasUniformPayoffs (admissible : ℝ → G.Profile → Prop) : Prop :=
  ∃ v : I → S → ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ σ : G.Profile, admissible ε σ ∧ G.UniformWitness σ v ε

/-- Nash incentives and payoff approximation for a specified, actual long-run evaluation. -/
def LongRunWitness (evaluation : LongRunEvaluation) (σ : G.Profile)
    (v : I → S → ℝ) (ε : ℝ) : Prop :=
  ∀ (s : S) (i : I),
    |G.longRunPayoff evaluation s σ i - v i s| ≤ ε ∧
      ∀ τ : G.Strategy i,
        G.longRunPayoff evaluation s (G.revise σ i τ) i ≤
          G.longRunPayoff evaluation s σ i + ε

/-- Approximate equilibrium payoffs for either lower-limit evaluation, kept separate. -/
def HasLongRunPayoffs (evaluation : LongRunEvaluation)
    (admissible : ℝ → G.Profile → Prop) : Prop :=
  ∃ v : I → S → ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ σ : G.Profile, admissible ε σ ∧ G.LongRunWitness evaluation σ v ε

/-- Own expected averages converge; deviations need not converge and are evaluated by limsup. -/
def MeanWitness (σ : G.Profile) (v : I → S → ℝ) (ε : ℝ) : Prop :=
  ∀ (s : S) (i : I), ∃ L : ℝ,
    Tendsto (fun N ↦ G.expectedAverage s σ i N) atTop (𝓝 L) ∧
      |L - v i s| ≤ ε ∧ ∀ τ : G.Strategy i,
        G.limsupExpected s (G.revise σ i τ) i ≤ L + ε

/-- Limiting expected-average payoffs with unrestricted upper-limit deviations. -/
def HasMeanPayoffs (admissible : ℝ → G.Profile → Prop) : Prop :=
  ∃ v : I → S → ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ σ : G.Profile, admissible ε σ ∧ G.MeanWitness σ v ε

/-- Forgetting a restriction on witnesses preserves uniform existence. -/
theorem HasUniformPayoffs.mono {P Q : ℝ → G.Profile → Prop}
    (h : G.HasUniformPayoffs P) (hPQ : ∀ ε σ, P ε σ → Q ε σ) :
    G.HasUniformPayoffs Q := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun ε hε ↦ ?_⟩
  obtain ⟨σ, hσ, hw⟩ := hv ε hε
  exact ⟨σ, hPQ ε σ hσ, hw⟩

/-- Forgetting a witness restriction preserves existence for the same lower-limit evaluation. -/
theorem HasLongRunPayoffs.mono (evaluation : LongRunEvaluation)
    {P Q : ℝ → G.Profile → Prop} (h : G.HasLongRunPayoffs evaluation P)
    (hPQ : ∀ ε σ, P ε σ → Q ε σ) : G.HasLongRunPayoffs evaluation Q := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun ε hε ↦ ?_⟩
  obtain ⟨σ, hσ, hw⟩ := hv ε hε
  exact ⟨σ, hPQ ε σ hσ, hw⟩

/-- Forgetting a witness restriction preserves limiting expected-average existence. -/
theorem HasMeanPayoffs.mono {P Q : ℝ → G.Profile → Prop}
    (h : G.HasMeanPayoffs P) (hPQ : ∀ ε σ, P ε σ → Q ε σ) :
    G.HasMeanPayoffs Q := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun ε hε ↦ ?_⟩
  obtain ⟨σ, hσ, hw⟩ := hv ε hε
  exact ⟨σ, hPQ ε σ hσ, hw⟩

end StochasticGame.Game
