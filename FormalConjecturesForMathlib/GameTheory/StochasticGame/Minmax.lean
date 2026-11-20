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
# Minmax benchmarks and finite-prefix deviations

The benchmark takes the infimum over independent behavioral strategies of the other players,
then the supremum over the given player's strategies. The defining sets are nonempty and
bounded. Every payoff below is the expectation of a pathwise lower limit of averages.

References: Flesch–Solan, *Stochastic Games with General Payoff Functions*,
https://arxiv.org/abs/2208.12096, equation (1) and Theorem 4.4 in version 1;
the finite-deviation selection criterion in Econ-1(e),
https://we-solve.github.io/problems/equilibrium-payoffs-in-finite-multiplayer-stochastic-games/.
-/

@[expose] public section

namespace StochasticGame.Game

variable {I S : Type} (G : StochasticGame.Game I S)

/-- Independent behavioral strategies of every player except `i`. -/
abbrev Opponents (i : I) := ∀ j : {j : I // j ≠ i}, G.Strategy j.val

instance opponentsNonempty (i : I) : Nonempty (G.Opponents i) := Pi.instNonempty

/-- Combine one player's strategy with the strategies of all other players. -/
noncomputable def withOpponents (i : I) (τ : G.Strategy i) (ρ : G.Opponents i) : G.Profile :=
  by
    classical
    exact fun j ↦ if h : j = i then h.symm ▸ τ else ρ ⟨j, h⟩

@[simp]
theorem withOpponents_self (i : I) (τ : G.Strategy i) (ρ : G.Opponents i) :
    G.withOpponents i τ ρ i = τ := by
  classical
  simp [withOpponents]

@[simp]
theorem withOpponents_other (i : I) (τ : G.Strategy i) (ρ : G.Opponents i)
    (j : {j : I // j ≠ i}) : G.withOpponents i τ ρ j.val = ρ j := by
  classical
  simp [withOpponents, j.property]

/-- A one-player game has only one opponent profile: the empty product. -/
theorem opponents_eq_of_subsingleton [Subsingleton I] (i : I) (ρ ρ' : G.Opponents i) :
    ρ = ρ' := by
  funext j
  exact (j.property (Subsingleton.elim j.val i)).elim

/-- Follow `τ` for the first `N` stages, then use `σ` at the complete actual history. -/
def prefixSplice (i : I) (τ σ : G.Strategy i) (N : ℕ) : G.Strategy i :=
  fun h ↦ if h.length < N then τ h else σ h

theorem prefixSplice_before (i : I) (τ σ : G.Strategy i) (N : ℕ) (h : G.History)
    (hN : h.length < N) : G.prefixSplice i τ σ N h = τ h := by
  simp [prefixSplice, hN]

/-- Returning to the original strategy keeps the history produced during the deviation. -/
theorem prefixSplice_after (i : I) (τ σ : G.Strategy i) (N : ℕ) (h : G.History)
    (hN : N ≤ h.length) : G.prefixSplice i τ σ N h = σ h := by
  simp [prefixSplice, Nat.not_lt.mpr hN]

@[simp]
theorem prefixSplice_zero (i : I) (τ σ : G.Strategy i) : G.prefixSplice i τ σ 0 = σ := by
  funext h
  simp [prefixSplice]

theorem prefixSplice_initial (i : I) (τ σ : G.Strategy i) {N : ℕ} (hN : 0 < N) (s : S) :
    G.prefixSplice i τ σ N (History.initial s) = τ (History.initial s) := by
  apply G.prefixSplice_before
  simpa using hN

variable [Fintype I] [Fintype S]

/-- Payoffs attainable by unilateral strategies against a fixed independent opponent profile. -/
def responsePayoffs (i : I) (s : S) (ρ : G.Opponents i) : Set ℝ :=
  Set.range fun τ : G.Strategy i ↦ G.longRunPayoff .pathLiminf s (G.withOpponents i τ ρ) i

theorem responsePayoffs_nonempty (i : I) (s : S) (ρ : G.Opponents i) :
    (G.responsePayoffs i s ρ).Nonempty := Set.range_nonempty _

theorem responsePayoffs_bddAbove (i : I) (s : S) (ρ : G.Opponents i) :
    BddAbove (G.responsePayoffs i s ρ) := by
  refine ⟨G.rewardBound, ?_⟩
  rintro _ ⟨τ, rfl⟩
  exact (abs_le.mp (G.norm_longRunPayoff_le .pathLiminf s _ i)).2

theorem responsePayoffs_bddBelow (i : I) (s : S) (ρ : G.Opponents i) :
    BddBelow (G.responsePayoffs i s ρ) := by
  refine ⟨-G.rewardBound, ?_⟩
  rintro _ ⟨τ, rfl⟩
  exact (abs_le.mp (G.norm_longRunPayoff_le .pathLiminf s _ i)).1

/-- Supremal payoff against fixed opponents, over unrestricted behavioral deviations. -/
noncomputable def bestResponseValue (i : I) (s : S) (ρ : G.Opponents i) : ℝ :=
  sSup (G.responsePayoffs i s ρ)

theorem payoff_le_bestResponseValue (i : I) (s : S) (ρ : G.Opponents i) (τ : G.Strategy i) :
    G.longRunPayoff .pathLiminf s (G.withOpponents i τ ρ) i ≤ G.bestResponseValue i s ρ :=
  le_csSup (G.responsePayoffs_bddAbove i s ρ) ⟨τ, rfl⟩

theorem bestResponseValue_le_rewardBound (i : I) (s : S) (ρ : G.Opponents i) :
    G.bestResponseValue i s ρ ≤ G.rewardBound := by
  apply csSup_le (G.responsePayoffs_nonempty i s ρ)
  rintro _ ⟨τ, rfl⟩
  exact (abs_le.mp (G.norm_longRunPayoff_le .pathLiminf s _ i)).2

theorem neg_rewardBound_le_bestResponseValue (i : I) (s : S) (ρ : G.Opponents i) :
    -G.rewardBound ≤ G.bestResponseValue i s ρ := by
  obtain ⟨τ⟩ := G.strategyNonempty i
  exact (abs_le.mp (G.norm_longRunPayoff_le .pathLiminf s _ i)).1.trans
    (G.payoff_le_bestResponseValue i s ρ τ)

/-- The collection of best-response values as the independent opponent profile varies. -/
def bestResponseValues (i : I) (s : S) : Set ℝ :=
  Set.range fun ρ : G.Opponents i ↦ G.bestResponseValue i s ρ

theorem bestResponseValues_nonempty (i : I) (s : S) :
    (G.bestResponseValues i s).Nonempty := Set.range_nonempty _

theorem bestResponseValues_bddBelow (i : I) (s : S) : BddBelow (G.bestResponseValues i s) := by
  refine ⟨-G.rewardBound, ?_⟩
  rintro _ ⟨ρ, rfl⟩
  exact G.neg_rewardBound_le_bestResponseValue i s ρ

theorem bestResponseValues_bddAbove (i : I) (s : S) : BddAbove (G.bestResponseValues i s) := by
  refine ⟨G.rewardBound, ?_⟩
  rintro _ ⟨ρ, rfl⟩
  exact G.bestResponseValue_le_rewardBound i s ρ

/-- The individual minmax benchmark: infimum over opponents, then supremum over the player. -/
noncomputable def minmax (i : I) (s : S) : ℝ := sInf (G.bestResponseValues i s)

theorem minmax_le_bestResponseValue (i : I) (s : S) (ρ : G.Opponents i) :
    G.minmax i s ≤ G.bestResponseValue i s ρ :=
  csInf_le (G.bestResponseValues_bddBelow i s) ⟨ρ, rfl⟩

theorem neg_rewardBound_le_minmax (i : I) (s : S) : -G.rewardBound ≤ G.minmax i s := by
  apply le_csInf (G.bestResponseValues_nonempty i s)
  rintro _ ⟨ρ, rfl⟩
  exact G.neg_rewardBound_le_bestResponseValue i s ρ

theorem minmax_le_rewardBound (i : I) (s : S) : G.minmax i s ≤ G.rewardBound := by
  obtain ⟨ρ⟩ := G.opponentsNonempty i
  exact (G.minmax_le_bestResponseValue i s ρ).trans (G.bestResponseValue_le_rewardBound i s ρ)

/-- Every feasible continuation is individually rational up to `η`. -/
def MinmaxAcceptable (σ : G.Profile) (η : ℝ) : Prop :=
  ∀ (i : I) (h : G.History), G.minmax i h.current - η ≤ G.expectedPathLiminfFrom h σ i

/-- One profile controls every positive finite-prefix deviation at the prescribed initial state. -/
def FinitePrefixControlled (s₀ : S) (σ : G.Profile) (η : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ (i : I) (τ : G.Strategy i),
    G.longRunPayoff .pathLiminf s₀ (G.revise σ i (G.prefixSplice i τ (σ i) N)) i ≤
      G.longRunPayoff .pathLiminf s₀ σ i + η

end StochasticGame.Game
