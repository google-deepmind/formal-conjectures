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
# Finite-memory equilibrium questions for stochastic games

Four separate questions restrict the witnessing profiles to clocked finite-private-memory
controllers with randomized updates. Deviations remain unrestricted behavioral strategies.

The clock and randomized updates follow Hansen, Ibsen-Jensen and Neyman, *The Big Match with
a Clock and a Bit of Memory*, §2.2 and Theorem 1, https://doi.org/10.1287/moor.2022.1267.
This formulation also lets the update use the observed next state, as chosen in issue
https://github.com/google-deepmind/formal-conjectures/issues/7959; that argument is absent
from the paper's §2.2 update kernel.
The multiplayer equilibrium questions are the finite-memory refinements in
https://we-solve.github.io/problems/equilibrium-payoffs-in-finite-multiplayer-stochastic-games/.

Stationary and clock-dependent Markov strategies have singleton memory. The Big Match obstructs
those restrictions and clock-independent finite memory in the standard uniform/limiting-average
setting. It does not refute this larger class: two memory states, randomized updates, and a clock
suffice for that game. No negative claim is transferred between payoff evaluations here.
-/

@[expose] public section

namespace StochasticFiniteMemory

open StochasticGame

/-- Does every finite stochastic game have uniform equilibrium payoffs witnessed by finite
private-memory strategies with a clock and randomized updates? -/
@[category research open, question, AMS 60 91]
theorem uniform_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasUniformPayoffs (fun _ σ ↦ G.FiniteMemoryRealizable σ) := by sorry

/-- Does the expectation-of-pathwise-liminf evaluation admit equilibrium payoffs with the same
finite-memory strategy restriction? -/
@[category research open, question, AMS 60 91]
theorem path_liminf_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasLongRunPayoffs .pathLiminf (fun _ σ ↦ G.FiniteMemoryRealizable σ) := by sorry

/-- Does the liminf-of-expected-averages evaluation admit equilibrium payoffs witnessed by
clocked finite-memory strategies? -/
@[category research open, question, AMS 60 91]
theorem expected_liminf_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasLongRunPayoffs .expectedLiminf (fun _ σ ↦ G.FiniteMemoryRealizable σ) := by sorry

/-- Can clocked finite-memory witnesses have convergent expected averages, with every
unrestricted deviation's upper limiting expected average within $\varepsilon$? -/
@[category research open, question, AMS 60 91]
theorem limiting_mean_equilibrium :
    ∀ (I S : Type) [Fintype I] [Nonempty I] [Fintype S] [Nonempty S] (G : Game I S),
      G.HasMeanPayoffs (fun _ σ ↦ G.FiniteMemoryRealizable σ) := by sorry

end StochasticFiniteMemory
