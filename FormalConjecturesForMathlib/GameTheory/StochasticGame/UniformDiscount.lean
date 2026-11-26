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
# Joint uniformity for Cesàro and discounted stochastic-game payoffs

One profile that is uniform for sufficiently large horizons also works for sufficiently small
discount rates after shrinking the error tolerance. The rate threshold is common to all initial
states, players, and behavioral deviations.

Reference: Neyman, *Robust Optimization in Stochastic Games*, §3.6,
https://arxiv.org/abs/2611.01151. The bridge uses Abel summation for bounded rewards.
-/

@[expose] public section

open BoundedPayoffs

namespace StochasticGame.Game

variable {I S : Type} [Fintype I] [Fintype S]
variable (G : StochasticGame.Game I S)

/-- The same profile approximates `v` and is Nash for every sufficiently small discount rate. -/
def DiscountWitness (σ : G.Profile) (v : I → S → ℝ) (ε : ℝ) : Prop :=
  ∃ rate₀ : ℝ, 0 < rate₀ ∧ rate₀ < 1 ∧
    ∀ rate : ℝ, 0 < rate → rate ≤ rate₀ → ∀ (s : S) (i : I),
      |G.expectedDiscounted s σ i rate - v i s| ≤ ε ∧
        ∀ τ : G.Strategy i,
          G.expectedDiscounted s (G.revise σ i τ) i rate ≤
            G.expectedDiscounted s σ i rate + ε

/-- One payoff vector and profile work for both large horizons and small discount rates. -/
def JointUniformWitness (σ : G.Profile) (v : I → S → ℝ) (ε : ℝ) : Prop :=
  G.UniformWitness σ v ε ∧ G.DiscountWitness σ v ε

/-- Joint uniform equilibrium payoffs, with an error-independent witness class. -/
def HasJointUniformPayoffs (admissible : G.Profile → Prop) : Prop :=
  ∃ v : I → S → ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ σ : G.Profile, admissible σ ∧ G.JointUniformWitness σ v ε

theorem UniformWitness.mono {σ : G.Profile} {v : I → S → ℝ} {ε δ : ℝ}
    (h : G.UniformWitness σ v ε) (hεδ : ε ≤ δ) : G.UniformWitness σ v δ := by
  obtain ⟨N₀, hN₀, hw⟩ := h
  refine ⟨N₀, hN₀, fun s i N hN ↦ ?_⟩
  obtain ⟨ha, hd⟩ := hw s i N hN
  exact ⟨ha.trans hεδ, fun τ ↦ (hd τ).trans (by linarith)⟩

/-- The discount-rate convention gives an Abel mixture of positive-horizon expected averages. -/
theorem expectedDiscounted_eq_abel (s : S) (σ : G.Profile) (i : I) {rate : ℝ}
    (hrate : 0 < rate) (hrate' : rate < 1) :
    G.expectedDiscounted s σ i rate =
      ∑' n, abelWeight rate n * G.expectedAverage s σ i (n + 1) :=
  (G.rewardProcess i).expected_abel_identity (G.law s σ) hrate hrate'

theorem expectedDiscounted_sub_const_eq_abel (s : S) (σ : G.Profile) (i : I)
    (c : ℝ) {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) :
    G.expectedDiscounted s σ i rate - c =
      ∑' n, abelWeight rate n * (G.expectedAverage s σ i (n + 1) - c) := by
  have ha := summable_abel_mul_of_bound hrate hrate'
    (fun n ↦ G.norm_expectedAverage_le s σ i (n + 1))
  have hc := (hasSum_abelWeight hrate hrate').summable.mul_right c
  calc
    _ = (∑' n, abelWeight rate n * G.expectedAverage s σ i (n + 1)) -
        ∑' n, abelWeight rate n * c := by
      rw [G.expectedDiscounted_eq_abel s σ i hrate hrate', tsum_mul_right,
        (hasSum_abelWeight hrate hrate').tsum_eq, one_mul]
    _ = _ := by rw [← ha.tsum_sub hc]; simp_rw [mul_sub]

theorem expectedDiscounted_sub_eq_abel (s : S) (σ τ : G.Profile) (i : I)
    {rate : ℝ} (hrate : 0 < rate) (hrate' : rate < 1) :
    G.expectedDiscounted s σ i rate - G.expectedDiscounted s τ i rate =
      ∑' n, abelWeight rate n *
        (G.expectedAverage s σ i (n + 1) - G.expectedAverage s τ i (n + 1)) := by
  have hσ := summable_abel_mul_of_bound hrate hrate'
    (fun n ↦ G.norm_expectedAverage_le s σ i (n + 1))
  have hτ := summable_abel_mul_of_bound hrate hrate'
    (fun n ↦ G.norm_expectedAverage_le s τ i (n + 1))
  rw [G.expectedDiscounted_eq_abel s σ i hrate hrate',
    G.expectedDiscounted_eq_abel s τ i hrate hrate', ← hσ.tsum_sub hτ]
  simp_rw [mul_sub]

/-- Halving the horizon error yields the joint formulation, with a common discount threshold. -/
theorem UniformWitness.joint_of_half {σ : G.Profile} {v : I → S → ℝ} {ε : ℝ}
    (hε : 0 < ε) (h : G.UniformWitness σ v (ε / 2)) :
    G.JointUniformWitness σ v ε := by
  have hδ : 0 < ε / 2 := by positivity
  have hfinite : G.UniformWitness σ v ε := UniformWitness.mono G h (by linarith)
  obtain ⟨N₀, hN₀, hw⟩ := h
  have hv (s : S) (i : I) : ‖v i s‖ ≤ G.rewardBound + ε / 2 := by
    have ha := (hw s i N₀ le_rfl).1
    have hb := G.norm_expectedAverage_le s σ i N₀
    rw [Real.norm_eq_abs, abs_le] at hb ⊢
    rw [abs_le] at ha
    constructor <;> linarith
  obtain ⟨r₁, hr₁, hr₁', hcenter⟩ :=
    exists_abel_mixture_norm_bound (B := 2 * G.rewardBound + ε) hδ N₀
  obtain ⟨r₂, hr₂, hr₂', hregret⟩ :=
    exists_abel_mixture_bound (B := 2 * G.rewardBound + ε) hδ N₀
  refine ⟨hfinite, min r₁ r₂, lt_min hr₁ hr₂,
    lt_of_le_of_lt (min_le_left _ _) hr₁', ?_⟩
  intro rate hrate hsmall s i
  have hrate' : rate < 1 := lt_of_le_of_lt (hsmall.trans (min_le_left _ _)) hr₁'
  have hc := hcenter rate hrate (hsmall.trans (min_le_left _ _))
    (fun n ↦ G.expectedAverage s σ i (n + 1) - v i s)
    (fun n ↦ (norm_sub_le _ _).trans ((add_le_add
      (G.norm_expectedAverage_le s σ i (n + 1)) (hv s i)).trans (by linarith)))
    (fun n hn ↦ by simpa [Real.norm_eq_abs] using (hw s i (n + 1) (by omega)).1)
  rw [← G.expectedDiscounted_sub_const_eq_abel s σ i (v i s) hrate hrate',
    Real.norm_eq_abs] at hc
  refine ⟨hc.trans (by linarith), fun τ ↦ ?_⟩
  have hd := hregret rate hrate (hsmall.trans (min_le_right _ _))
    (fun n ↦ G.expectedAverage s (G.revise σ i τ) i (n + 1) -
      G.expectedAverage s σ i (n + 1))
    (fun n ↦ (norm_sub_le _ _).trans ((add_le_add
      (G.norm_expectedAverage_le s (G.revise σ i τ) i (n + 1))
      (G.norm_expectedAverage_le s σ i (n + 1))).trans (by linarith)))
    (fun n hn ↦ by have := (hw s i (n + 1) (by omega)).2 τ; linarith)
  rw [← G.expectedDiscounted_sub_eq_abel s (G.revise σ i τ) σ i hrate hrate'] at hd
  linarith

/-- Reindexing the tolerance makes the large-horizon and joint formulations equivalent. -/
theorem hasUniformPayoffs_iff_joint (P : G.Profile → Prop) :
    G.HasUniformPayoffs (fun _ σ ↦ P σ) ↔ G.HasJointUniformPayoffs P := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, fun ε hε ↦ ?_⟩
    obtain ⟨σ, hP, hw⟩ := hv (ε / 2) (by positivity)
    exact ⟨σ, hP, UniformWitness.joint_of_half G hε hw⟩
  · rintro ⟨v, hv⟩
    refine ⟨v, fun ε hε ↦ ?_⟩
    obtain ⟨σ, hP, hw⟩ := hv ε hε
    exact ⟨σ, hP, hw.1⟩

/-- Constant rewards give a uniform witness for any profile and every nonnegative tolerance. -/
theorem uniformWitness_of_constant_reward (σ : G.Profile) (c : I → ℝ)
    (hc : ∀ i s a, G.reward i s a = c i) {ε : ℝ} (hε : 0 ≤ ε) :
    G.UniformWitness σ (fun i _ ↦ c i) ε := by
  refine ⟨1, le_rfl, fun s i N hN ↦ ?_⟩
  have havg (ρ : G.Profile) : G.expectedAverage s ρ i N = c i :=
    G.expectedAverageFrom_of_constant_reward i (c i) (hc i) _ ρ (by omega)
  rw [havg σ, sub_self, abs_zero]
  exact ⟨hε, fun τ ↦ by rw [havg (G.revise σ i τ)]; linarith⟩

/-- The joint formulation has the expected constant-reward normalization. -/
theorem jointUniformWitness_of_constant_reward (σ : G.Profile) (c : I → ℝ)
    (hc : ∀ i s a, G.reward i s a = c i) {ε : ℝ} (hε : 0 < ε) :
    G.JointUniformWitness σ (fun i _ ↦ c i) ε :=
  UniformWitness.joint_of_half G hε
    (G.uniformWitness_of_constant_reward σ c hc (by positivity))

end StochasticGame.Game
