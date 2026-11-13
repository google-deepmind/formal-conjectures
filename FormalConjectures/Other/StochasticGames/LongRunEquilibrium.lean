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
# Three long-run stochastic-game equilibrium questions

These questions distinguish $\mathbb E[\liminf_N\bar g_N]$ from
$\liminf_N\mathbb E[\bar g_N]$. The third requires convergence of the profile's expected
averages and evaluates unrestricted deviations by their upper limits. It is an explicit
convention for the limiting-average question, not an identification of the evaluations.

*Sources:*
- [Econ-1, part (c)](https://we-solve.github.io/problems/equilibrium-payoffs-in-finite-multiplayer-stochastic-games/).
- Flesch–Solan, *Stochastic Games with General Payoff Functions*,
  [arXiv:2208.12096v1, Corollary 4.10](https://arxiv.org/pdf/2208.12096v1#page=16).
  That result concerns some initial state for bounded shift-invariant path payoffs. These
  questions require one profile for all initial states. A lower limit of expectations is a
  functional of the play law, rather than a specified path payoff.
-/

@[expose] public section

namespace StochasticLongRun

/-- Does every finite stochastic game admit approximate equilibrium payoffs for
$\mathbb E[\liminf_N\bar g_N]$, with a fixed state-indexed vector before the tolerance? -/
@[category research open, question, AMS 60 91]
theorem expected_path_liminf_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S]
      (G : StochasticGame.Game I S),
      G.HasLongRunPayoffs .pathLiminf (fun _ _ ↦ True) := by
  sorry

/-- Does every finite stochastic game admit approximate equilibrium payoffs for
$\liminf_N\mathbb E[\bar g_N]$? Its payoff vector and profiles are independent of the first
question's witnesses. -/
@[category research open, question, AMS 60 91]
theorem liminf_expected_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S]
      (G : StochasticGame.Game I S),
      G.HasLongRunPayoffs .expectedLiminf (fun _ _ ↦ True) := by
  sorry

/-- Does every finite stochastic game admit a fixed state-indexed payoff vector approximated
by profiles whose expected averages converge, with each unrestricted deviation's upper
limiting expected average at most the profile's limit plus $\varepsilon$? -/
@[category research open, question, AMS 60 91]
theorem convergent_expected_average_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S]
      (G : StochasticGame.Game I S),
      G.HasMeanPayoffs (fun _ _ ↦ True) := by
  sorry

end StochasticLongRun
