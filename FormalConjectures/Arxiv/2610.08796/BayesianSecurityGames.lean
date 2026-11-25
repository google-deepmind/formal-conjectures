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
# Computing Bayes–Nash equilibria in Bayesian simple security games

The source lists the game data explicitly and leaves the numerical encoding implicit.
We use rational payoffs and probabilities. `BitstringEncoding` encodes each rational by its
reduced numerator and positive denominator. The time bound is polynomial in the bit length of
the encoded input, which includes the resource count and all table entries.

The defender chooses exactly $r$ distinct targets. We represent her mixed strategy by the
coverage probability of each target, with entries in $[0,1]$ that sum to $r$. In this model,
these marginals can be converted in polynomial time to a sparse mixture of legal allocations.

*References:*
- Vincent Conitzer, *Computing Bayes–Nash equilibrium in simple security games*,
  [§1](https://arxiv.org/pdf/2610.08796#page=1).
- Joshua Letchford and Vincent Conitzer, *Solving Security Games on Graphs via Marginal
  Probabilities*. [Paper](https://cdn.aaai.org/ojs/8688/8688-13-12216-1-2-20201228.pdf).
-/

@[expose] public section

open ComplexityTheory

namespace Arxiv.«2610.08796»

/-- The payoffs at an uncovered target and at a covered target, in that order. -/
abbrev PayoffPair := ℚ × ℚ

/-- The resource count, defender payoff table, and list of attacker types.
Each type gives its prior probability and its payoff table in target order. -/
abbrev GameInput := ℕ × List PayoffPair × List (ℚ × List PayoffPair)

/-- Defender coverage marginals and one target distribution per attacker type. -/
abbrev EquilibriumOutput := List ℚ × List (List ℚ)

namespace GameInput

/-- The number of targets. -/
def numTargets (g : GameInput) : ℕ := g.2.1.length

/-- The number of attacker types. -/
def numTypes (g : GameInput) : ℕ := g.2.2.length

/-- The defender payoffs at a target. -/
def defenderPayoff (g : GameInput) (t : Fin g.numTargets) : PayoffPair := g.2.1.get t

/-- The prior probability of an attacker type. -/
def prior (g : GameInput) (θ : Fin g.numTypes) : ℚ := (g.2.2.get θ).1

/-- The attacker payoff table for one type. -/
def attackerPayoffs (g : GameInput) (θ : Fin g.numTypes) : List PayoffPair := (g.2.2.get θ).2

/-- The attacker payoffs at a target. A missing entry is possible only for an invalid game. -/
def attackerPayoff (g : GameInput) (θ : Fin g.numTypes) (t : Fin g.numTargets) : PayoffPair :=
  (g.attackerPayoffs θ)[t.val]?.getD (0, 0)

/-- The game has at least one target for the attacker to choose, a valid resource count and
prior, and complete payoff tables with the required monotonicity under coverage. -/
def Valid (g : GameInput) : Prop :=
  0 < g.numTargets ∧ g.1 ≤ g.numTargets ∧
  (∑ θ : Fin g.numTypes, g.prior θ) = 1 ∧
  (∀ t : Fin g.numTargets, (g.defenderPayoff t).1 ≤ (g.defenderPayoff t).2) ∧
  ∀ θ : Fin g.numTypes, 0 ≤ g.prior θ ∧ (g.attackerPayoffs θ).length = g.numTargets ∧
    ∀ t : Fin g.numTargets, (g.attackerPayoff θ t).2 ≤ (g.attackerPayoff θ t).1

/-- For a valid game, the profile is feasible and each player's strategy is a best response.
Each attacker type assigns positive probability only to targets that maximize its expected
payoff. We impose this even at zero prior, since those choices have no effect on the defender's
payoff. The defender's payoff is linear in coverage, so it suffices to check that shifting
coverage between any two targets cannot improve it. -/
def IsBayesNash (g : GameInput) (e : EquilibriumOutput) : Prop :=
  let coverage (t : Fin g.numTargets) := e.1[t.val]?.getD 0
  let row (θ : Fin g.numTypes) := e.2[θ.val]?.getD []
  let attackProb (θ : Fin g.numTypes) (t : Fin g.numTargets) := (row θ)[t.val]?.getD 0
  let attackUtility (θ : Fin g.numTypes) (t : Fin g.numTargets) :=
    let (uncovered, covered) := g.attackerPayoff θ t
    (1 - coverage t) * uncovered + coverage t * covered
  let coverageGain (t : Fin g.numTargets) :=
    let (uncovered, covered) := g.defenderPayoff t
    (∑ θ : Fin g.numTypes, g.prior θ * attackProb θ t) * (covered - uncovered)
  e.1.length = g.numTargets ∧ e.2.length = g.numTypes ∧
  (∑ t, coverage t) = (g.1 : ℚ) ∧
  (∀ t, 0 ≤ coverage t ∧ coverage t ≤ 1) ∧
  (∀ θ, (row θ).length = g.numTargets ∧ (∑ t, attackProb θ t) = 1 ∧
    ∀ t, 0 ≤ attackProb θ t) ∧
  (∀ θ t s, 0 < attackProb θ t → attackUtility θ s ≤ attackUtility θ t) ∧
  (∀ t s, 0 < coverage t → coverage s < 1 → coverageGain s ≤ coverageGain t)

end GameInput

/-- Can one deterministic polynomial-time algorithm compute an exact Bayes–Nash equilibrium
for every Bayesian simple security game? -/
@[category research open, question, AMS 68 91]
theorem exists_isPolyTime_bayesNash :
    ∃ solve : GameInput → EquilibriumOutput,
      IsPolyTime solve ∧ ∀ (g : GameInput), g.Valid → g.IsBayesNash (solve g) := by
  sorry

end Arxiv.«2610.08796»
