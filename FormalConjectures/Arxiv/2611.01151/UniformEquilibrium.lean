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
# Uniform equilibrium payoffs in finite stochastic games

Sources: Neyman, *Robust Optimization in Stochastic Games*, introduction and §3.6, Definition 11,
https://arxiv.org/abs/2611.01151; Solan–Vieille, *Stochastic games* (2015),
https://pmc.ncbi.nlm.nih.gov/articles/PMC4653174/.

Players and states are nonempty and finite. Available actions are finite and nonempty at each
state. Public states and realized actions determine the history; behavioral randomization is
independent across players. Deviations are unrestricted behavioral strategies.
The incentive inequality uses regret relative to the profile payoff. Rescaling the tolerance gives
Definition 11's comparison with the target vector.

`StochasticGame.Game.hasUniformPayoffs_iff_joint` gives the equivalent formulation requiring
the same profile for sufficiently large horizons and sufficiently small discount rates.
-/

@[expose] public section

namespace StochasticUniformEquilibrium

/-- Does every finite stochastic game have a state-indexed payoff vector such that, for each
$\varepsilon>0$, one profile is $\varepsilon$-Nash and approximates that vector for all initial
states and all sufficiently large horizons? The vector precedes $\varepsilon$, and the profile
cannot depend on the horizon. -/
@[category research open, question, AMS 60 91]
theorem uniform_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S]
      (G : StochasticGame.Game I S), G.HasUniformPayoffs (fun _ _ ↦ True) := by
  sorry

end StochasticUniformEquilibrium
