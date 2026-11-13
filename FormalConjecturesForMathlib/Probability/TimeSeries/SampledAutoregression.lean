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

public import FormalConjecturesForMathlib.Probability.TimeSeries.Autoregression
public import Mathlib.Algebra.Ring.Parity

/-!
# Observed laws of sampled autoregressions

Snapshots and nonoverlapping block sums are measurable maps on integer-indexed real paths.
The identified set includes all stationary coefficient vectors of order at most `p` and all
positive innovation variances that can produce the same observed path law.

*Reference:* M. Mlikota, [Parameter Identification and Inference in Discretely Sampled or
Temporally Aggregated Autoregressions](https://arxiv.org/abs/2608.13224v2), equations (2)–(3)
and §3.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace TimeSeries.Autoregression

/-- Stock observations: $y_t=x_{qt}$. -/
def snapshot (q : ℕ) (x : Path) : Path := fun t ↦ x ((q : ℤ) * t)

/-- Flow observations: $y_t=\sum_{s=0}^{q-1}x_{qt-s}$. -/
def blockSum (q : ℕ) (x : Path) : Path :=
  fun t ↦ ∑ s ∈ Finset.range q, x ((q : ℤ) * t - s)

@[fun_prop]
lemma measurable_snapshot (q : ℕ) : Measurable (snapshot q) := by
  fun_prop [snapshot]

@[fun_prop]
lemma measurable_blockSum (q : ℕ) : Measurable (blockSum q) := by
  fun_prop [blockSum]

@[simp]
lemma snapshot_one : snapshot 1 = id := by
  funext x t
  simp [snapshot]

@[simp]
lemma blockSum_one : blockSum 1 = id := by
  funext x t
  simp [blockSum]

/-- Both observation schemes at frequency one preserve the full latent path law. -/
lemma observation_laws_one (μ : Measure Path) :
    μ.map (snapshot 1) = μ ∧ μ.map (blockSum 1) = μ := by
  simp

/-- Multiplication of the path at time `t` by $(-1)^t$. -/
def signFlipPath (x : Path) : Path := fun t ↦ (-1 : ℝ) ^ t * x t

@[fun_prop]
lemma measurable_signFlipPath : Measurable signFlipPath := by
  fun_prop [signFlipPath]

/-- Even-frequency snapshots cannot see the alternating time-sign transformation. -/
lemma snapshot_signFlipPath_of_even {q : ℕ} (hq : Even q) (x : Path) :
    snapshot q (signFlipPath x) = snapshot q x := by
  funext t
  simp only [snapshot, signFlipPath, zpow_mul, zpow_natCast, hq.neg_one_pow,
    one_zpow, one_mul]

/-- Block sums and snapshots give different observations even on a constant path. -/
lemma blockSum_two_ne_snapshot_two : blockSum 2 ≠ snapshot 2 := by
  intro h
  have := congrArg (fun f : Path → Path ↦ f (fun _ ↦ 1) 0) h
  norm_num [blockSum, snapshot, Finset.sum_range_succ] at this

/-- At even frequency two, block sums can detect the alternating time-sign transformation. -/
lemma blockSum_two_signFlipPath_const : blockSum 2 (signFlipPath (fun _ ↦ 1)) 0 = 0 := by
  norm_num [blockSum, signFlipPath, Finset.sum_range_succ]

/-- The candidate set compares actual observed path measures of Gaussian AR models.

There is no exact-order, powered-root, or variance-equality restriction on a competitor.
-/
def identifiedSet {p : ℕ} (observation : Path → Path) (μ : Measure Path) :
    Set (Parameter p) :=
  {θ | θ.IsStationary ∧ ∃ ν : Measure Path,
    IsGaussianARLaw θ ν ∧ ν.map observation = μ.map observation}

/-- The identified set under observation every `q` periods. -/
def stockIdentifiedSet (p q : ℕ) (μ : Measure Path) : Set (Parameter p) :=
  identifiedSet (snapshot q) μ

/-- The identified set under nonoverlapping sums of `q` consecutive periods. -/
def flowIdentifiedSet (p q : ℕ) (μ : Measure Path) : Set (Parameter p) :=
  identifiedSet (blockSum q) μ

/-- A stationary true parameter is in its own identified set for every observation map. -/
lemma mem_identifiedSet_self {p : ℕ} {θ : Parameter p} {μ : Measure Path}
    (hs : θ.IsStationary) (hμ : IsGaussianARLaw θ μ) (observation : Path → Path) :
    θ ∈ identifiedSet observation μ :=
  ⟨hs, μ, hμ, rfl⟩

/-- At frequency one the stock and flow identified sets agree. -/
lemma stockIdentifiedSet_one_eq_flowIdentifiedSet (p : ℕ) (μ : Measure Path) :
    stockIdentifiedSet p 1 μ = flowIdentifiedSet p 1 μ := by
  simp [stockIdentifiedSet, flowIdentifiedSet]

/-- A root factorization with nonzero stationary dynamic roots and distinct `q`th powers.

The dynamic roots are reciprocals of the zeros of the autoregressive polynomial.
-/
def Parameter.HasDistinctPoweredRoots {p : ℕ} (θ : Parameter p) (q : ℕ) : Prop :=
  ∃ roots : Fin p → ℂ,
    θ.polynomial = ∏ i : Fin p, (1 - Polynomial.C (roots i) * Polynomial.X) ∧
    (∀ i, roots i ≠ 0 ∧ ‖roots i‖ < 1) ∧ Function.Injective (fun i ↦ roots i ^ q)

/-- Distinct even-powered dynamic roots force the sign transform to be a different parameter. -/
lemma Parameter.signFlip_ne_of_distinctPoweredRoots {p q : ℕ} {θ : Parameter p}
    (hp : 0 < p) (hq : Even q) (hroots : θ.HasDistinctPoweredRoots q) :
    θ.signFlip ≠ θ := by
  obtain ⟨roots, hfactor, hnonzero, hinj⟩ := hroots
  let i : Fin p := ⟨0, hp⟩
  have hi : roots i ≠ 0 := (hnonzero i).1
  have hzero : θ.polynomial.eval (roots i)⁻¹ = 0 := by
    rw [hfactor, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]
  intro hflip
  have hnegzero : θ.polynomial.eval (-(roots i)⁻¹) = 0 := by
    rw [← Parameter.eval_polynomial_signFlip, hflip]
    exact hzero
  rw [hfactor, Polynomial.eval_prod] at hnegzero
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hnegzero
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at hj
  have hij : roots j = -roots i := by
    field_simp [hi] at hj
    linear_combination hj
  have hji : j = i := hinj (by
    change roots j ^ q = roots i ^ q
    rw [hij, hq.neg_pow])
  rw [hji] at hij
  apply hi
  linear_combination (1 / 2 : ℂ) * hij

/-- A nonzero stationary lag-one parameter satisfies the powered-root condition at every
frequency. -/
lemma firstOrder_hasDistinctPoweredRoots {a : ℝ} (ha : a ≠ 0) (ha' : |a| < 1)
    (v : ℝ≥0) (hv : 0 < v) (q : ℕ) :
    (firstOrder a v hv).HasDistinctPoweredRoots q := by
  refine ⟨fun _ ↦ (a : ℂ), ?_, ?_, ?_⟩
  · simp
  · intro i
    change (a : ℂ) ≠ 0 ∧ ‖(a : ℂ)‖ < 1
    exact ⟨by exact_mod_cast ha, by simpa using ha'⟩
  · intro i j _
    exact Subsingleton.elim i j

end TimeSeries.Autoregression
