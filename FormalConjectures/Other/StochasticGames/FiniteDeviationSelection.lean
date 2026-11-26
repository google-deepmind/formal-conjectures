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
# Minmax-acceptable play with control of finite-prefix deviations

This is the selection question in Econ-1(e),
https://we-solve.github.io/problems/equilibrium-payoffs-in-finite-multiplayer-stochastic-games/.

The evaluation is $\mathbb E[\liminf_N N^{-1}\sum_{t=1}^N g_i(s_t,a_t)]$ throughout.
Flesch–Solan, *Stochastic Games with General Payoff Functions*,
https://arxiv.org/abs/2208.12096v1, Theorem 4.4, proves minmax acceptability alone.
Its some-subgame equilibrium result does not supply the simultaneous selection at a prescribed
initial state asked for here. This criterion is separate from uniform equilibrium existence.
-/

@[expose] public section

namespace StochasticFiniteDeviationSelection

/-- Does every finite stochastic game and prescribed initial state admit, for each $\eta>0$,
one profile that is minmax-acceptable after every feasible history and bounds each player's gain
from every finite-prefix deviation by $\eta$? The payoff remains infinite-horizon. -/
@[category research open, question, AMS 60 91]
theorem finite_deviation_selection :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S]
      (G : StochasticGame.Game I S) (s₀ : S) (η : ℝ), 0 < η →
      ∃ σ : G.Profile, G.MinmaxAcceptable σ η ∧ G.FinitePrefixControlled s₀ σ η := by
  sorry

end StochasticFiniteDeviationSelection
