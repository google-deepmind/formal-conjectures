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
# Subgame-perfect refinements of stochastic-game equilibrium existence

Eight separate questions refine the four payoff criteria, each with unrestricted or clocked
finite-memory witnesses. All unilateral deviations remain unrestricted. The same profile
satisfies the original initial-state payoff requirement and the continuation incentives.

After every feasible history, including profile-null histories, start a fresh law at the full
recorded history. Averaging restarts; the strategy clock and canonically filtered private memory
are retained. Uniform horizon thresholds may depend on the history. No continuation payoff
target or threshold uniform over all histories is required.

Source: [Econ-1(d)](https://we-solve.github.io/problems/equilibrium-payoffs-in-finite-multiplayer-stochastic-games/).
Flesch–Solan's discussion of general Borel payoffs,
https://arxiv.org/abs/2208.12096v1, does not substitute that broader model for finite Markovian
stage rewards. Solan–Vieille, *Quitting Games* (2001),
https://www.math.tau.ac.il/~eilons/quitting19.pdf, imposes additional payoff assumptions.
These are precise refinement questions, not unconditional existence results of those papers.
-/

@[expose] public section

namespace StochasticSubgamePerfect

open StochasticGame

/-- Does the uniform payoff question admit a profile with uniform Nash incentives in every
subgame, with the horizon threshold chosen separately at each history? -/
@[category research open, question, AMS 60 91]
theorem uniform_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasUniformPayoffs (fun ε σ ↦ G.SubgameUniform σ ε) := by
  sorry

/-- Does the same uniform subgame requirement admit clocked finite-memory witnesses? -/
@[category research open, question, AMS 60 91]
theorem finite_memory_uniform_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasUniformPayoffs
        (fun ε σ ↦ G.FiniteMemoryRealizable σ ∧ G.SubgameUniform σ ε) := by
  sorry

/-- Does the expected-pathwise-liminf payoff question admit an approximate Nash profile after
every feasible history? -/
@[category research open, question, AMS 60 91]
theorem path_liminf_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasLongRunPayoffs .pathLiminf
        (fun ε σ ↦ G.SubgameLongRun .pathLiminf σ ε) := by
  sorry

/-- Does that expected-pathwise-liminf subgame refinement admit finite-memory witnesses? -/
@[category research open, question, AMS 60 91]
theorem finite_memory_path_liminf_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasLongRunPayoffs .pathLiminf
        (fun ε σ ↦ G.FiniteMemoryRealizable σ ∧ G.SubgameLongRun .pathLiminf σ ε) := by
  sorry

/-- Does the liminf-of-expected-averages payoff question admit approximate Nash incentives
after every feasible history? -/
@[category research open, question, AMS 60 91]
theorem expected_liminf_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasLongRunPayoffs .expectedLiminf
        (fun ε σ ↦ G.SubgameLongRun .expectedLiminf σ ε) := by
  sorry

/-- Does the liminf-of-expectations subgame refinement admit finite-memory witnesses? -/
@[category research open, question, AMS 60 91]
theorem finite_memory_expected_liminf_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasLongRunPayoffs .expectedLiminf
        (fun ε σ ↦ G.FiniteMemoryRealizable σ ∧ G.SubgameLongRun .expectedLiminf σ ε) := by
  sorry

/-- Does the limiting expected-average question admit a profile whose own continuation
averages converge at every history, with all deviations evaluated by upper limits? -/
@[category research open, question, AMS 60 91]
theorem limiting_mean_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasMeanPayoffs (fun ε σ ↦ G.SubgameMean σ ε) := by
  sorry

/-- Does that convergent-mean subgame refinement admit clocked finite-memory witnesses? -/
@[category research open, question, AMS 60 91]
theorem finite_memory_limiting_mean_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasMeanPayoffs
        (fun ε σ ↦ G.FiniteMemoryRealizable σ ∧ G.SubgameMean σ ε) := by
  sorry

end StochasticSubgamePerfect
