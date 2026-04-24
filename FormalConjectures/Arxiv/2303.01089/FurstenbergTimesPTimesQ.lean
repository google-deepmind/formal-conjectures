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

import FormalConjectures.Util.ProblemImports

/-!
# Furstenberg's `times p, times q` conjectures

*Reference:* [arxiv/2303.01089](https://arxiv.org/abs/2303.01089)
**Around Furstenberg's Times p, Times q Conjecture: Times p-Invariant Measures with some Large
Fourier Coefficients**
by *Catalin Badea and Sophie Grivaux*
-/

noncomputable section

open Set Filter MeasureTheory AddCircle

namespace Arxiv.«2303.01089»

local notation "𝕋" => UnitAddCircle

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/--
Two integers `p, q ≥ 2` are multiplicatively independent if the only relation
`p ^ m = q ^ n` is the trivial one.
-/
def MultiplicativelyIndependent (p q : ℕ) : Prop :=
  ∀ m n : ℕ, p ^ m = q ^ n → m = 0 ∧ n = 0

/--
The map `T_n : 𝕋 → 𝕋` given by `x ↦ n x mod 1`.
-/
def T (n : ℕ) : 𝕋 → 𝕋 := fun x ↦ n • x

lemma continuous_T (n : ℕ) : Continuous (T n) := by
  fun_prop

/--
The image of a set under `T_n`.
-/
def TSet (n : ℕ) (F : Set 𝕋) : Set 𝕋 := T n '' F

/--
The push-forward of a probability measure under `T_n`.
-/
noncomputable def TMeasure (n : ℕ) (μ : ProbabilityMeasure 𝕋) : ProbabilityMeasure 𝕋 :=
  μ.map (continuous_T n).measurable.aemeasurable

/--
A subset of `𝕋` is `T_n`-invariant if `T_n(F) ⊆ F`.
-/
def IsTInvariantSet (n : ℕ) (F : Set 𝕋) : Prop :=
  TSet n F ⊆ F

/--
A probability measure on `𝕋` is continuous if it has no atoms.
-/
def IsContinuousProbabilityMeasure (μ : ProbabilityMeasure 𝕋) : Prop :=
  NoAtoms (μ : Measure 𝕋)

/--
A probability measure is `T_n`-invariant if its push-forward by `T_n` is itself.
-/
def IsTInvariantMeasure (n : ℕ) (μ : ProbabilityMeasure 𝕋) : Prop :=
  TMeasure n μ = μ

/--
The set `P_p(𝕋)` of `T_p`-invariant Borel probability measures on `𝕋`.
-/
def Pp (p : ℕ) : Set (ProbabilityMeasure 𝕋) :=
  {μ | IsTInvariantMeasure p μ}

/--
The set `P_{p,c}(𝕋)` of continuous `T_p`-invariant Borel probability measures on `𝕋`.
-/
def Ppc (p : ℕ) : Set (ProbabilityMeasure 𝕋) :=
  {μ | IsTInvariantMeasure p μ ∧ IsContinuousProbabilityMeasure μ}

/--
The normalized Lebesgue measure on `𝕋 = ℝ / ℤ`.
-/
noncomputable def lebesgue : ProbabilityMeasure 𝕋 :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

/--
The Weyl averages used in the paper's formulation of normality in base `q`.
-/
def normalityAverage (q : ℕ) (a : ℤ) (x : 𝕋) (N : ℕ) : ℂ :=
  ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N, fourier (a * (q ^ n : ℤ)) x

/--
A point of `𝕋` is normal in base `q` if all non-zero Weyl averages along `q^n` vanish.
-/
def IsNormalInBase (q : ℕ) (x : 𝕋) : Prop :=
  ∀ a : ℤ, a ≠ 0 → Tendsto (normalityAverage q a x) atTop (𝓝 0)

/--
**Conjecture 1.2**: if `F` is an infinite closed `T_p`-invariant subset of `𝕋`, then the sets
`T_{q^n}(F)` converge in Hausdorff distance to `𝕋`.
-/
@[category research open, AMS 11 37]
theorem conjecture_1_2
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : MultiplicativelyIndependent p q)
    {F : Set 𝕋} (hF_closed : IsClosed F) (hF_infinite : F.Infinite) (hF_tp : IsTInvariantSet p F) :
    Tendsto (fun n : ℕ ↦ Metric.hausdorffDist (TSet (q ^ n) F) Set.univ) atTop (𝓝 0) := by
  sorry

/--
**Conjecture 1.3** (`×p, ×q` conjecture): the only continuous Borel probability measure on `𝕋`
which is both `T_p`- and `T_q`-invariant is Lebesgue measure.
-/
@[category research open, AMS 11 37]
theorem conjecture_1_3
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : MultiplicativelyIndependent p q)
    (μ : ProbabilityMeasure 𝕋) (hμ : μ ∈ Ppc p) (hμ_tq : IsTInvariantMeasure q μ) :
    μ = lebesgue := by
  sorry

/--
**Conjecture 1.4**: if `μ` is a continuous `T_p`-invariant Borel probability measure on `𝕋`,
then `T_{q^n} μ` converges weak-star to Lebesgue measure.

This paper disproves the conjecture, so the recorded answer is `False`.
-/
@[category research solved, AMS 11 37]
theorem conjecture_1_4
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : MultiplicativelyIndependent p q) :
    answer(False) ↔
      ∀ μ : ProbabilityMeasure 𝕋, μ ∈ Ppc p →
        Tendsto (fun n : ℕ ↦ TMeasure (q ^ n) μ) atTop (𝓝 lebesgue) := by
  sorry

/--
**Conjecture 5.7**: for any `μ ∈ P_{p,c}(𝕋)`, `μ`-almost every point of `𝕋` is normal in base `q`.
-/
@[category research open, AMS 11 37]
theorem conjecture_5_7
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : MultiplicativelyIndependent p q)
    (μ : ProbabilityMeasure 𝕋) (hμ : μ ∈ Ppc p) :
    ∀ᵐ x ∂(μ : Measure 𝕋), IsNormalInBase q x := by
  sorry

end Arxiv.«2303.01089»
