/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjecturesUtil

/-!
# Erdős Problem 522

*Reference:* [erdosproblems.com/522](https://www.erdosproblems.com/522)
-/

open MeasureTheory Classical Filter
open scoped ProbabilityTheory Topology Real

namespace Erdos522

/--
A sequence of *Kac coefficients* over a subset `S` of a field `k` is a countably infinite sequence
of independent random variables, each uniformly distributed over `S`.

Such a sequence determines a *Kac polynomial* of degree `n` for each `n`, which is the random
polynomial given by `KacCoefficients.polynomial`.

Note: the uniformity hypothesis `h_unif` is relative to the reference measure `μ`. For the
discrete coefficient sets used in this file (`{-1, 1}`, `{0, 1}`), the statements below
instantiate `μ := Measure.count`, so that `h_unif` states that the law of each coefficient is
`ProbabilityTheory.uniformOn S`. The `volume` default would be degenerate here: a finite `S` is
`volume`-null, conditioning `volume` on it yields the zero measure, and no a.e.-measurable
coefficient has the zero measure as its law. See the regression witness
`coinKacCoefficients` below.
-/
@[ext]
structure KacCoefficients
    {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := by volume_tac) where
  toFun : ℕ → Ω → k
  h_indep : ProbabilityTheory.iIndepFun toFun ℙ
  h_unif : ∀ i, MeasureTheory.pdf.IsUniform (toFun i) S ℙ μ

variable {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := by volume_tac)

/--
We can always view a Kac polynomial as a random variable on `ℕ`.
-/
instance : FunLike (KacCoefficients S Ω μ) ℕ (Ω → k) where
  coe P := P.toFun
  coe_injective' := by intro P Q h ; aesop

namespace KacCoefficients

open scoped Polynomial

variable {S Ω} {μ : Measure k}

/--
The random polynomial associated to a sequence `c : KacCoefficients S Ω μ` of Kac coefficients
given by `∑ i ∈ Finset.range (n + 1), c i z^i`.
-/
noncomputable def polynomial (c : KacCoefficients S Ω μ) (n : ℕ) :
    Ω → k[X] := fun ω => ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (c i ω)

/--
The random multiset of roots associated to a Kac polynomial
-/
noncomputable def roots (c : KacCoefficients S Ω μ) (n : ℕ) : Ω → Multiset k :=
    fun ω => (c.polynomial n ω).roots

/-- Counts the number of roots of a Kac polynomial in the unit disk with multiplicity. -/
noncomputable def numRootsInUnitDisk [PseudoMetricSpace k] (c : KacCoefficients S Ω μ) (n : ℕ)
    (ω : Ω) : ℕ := (c.roots n ω).countP (· ∈ Metric.closedBall 0 1)

end KacCoefficients

/-!
### Regression witness

An honest Rademacher coefficient sequence — coordinate signs on the Bernoulli space
`ℕ → Bool` carrying the infinite product of fair coins — inhabits
`KacCoefficients ({-1, 1} : Set ℂ) (ℕ → Bool) Measure.count`, so the statements below
quantify over the intended instances. (With the previously elided `volume` default the
structure admitted no a.e.-measurable coefficients at all.)
-/

section RegressionWitness

/-- The fair coin measure on `Bool`: `½ (δ_false + δ_true)`. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac false + Measure.dirac true)

instance : IsProbabilityMeasure fairCoin := by
  refine ⟨?_⟩
  rw [fairCoin, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ,
    smul_eq_mul, one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The Bernoulli sequence space: `ℕ → Bool` carrying the infinite product of fair-coin
measures (Ionescu-Tulcea). Local instance — scoped to this section. -/
@[reducible] noncomputable def coinSpace : MeasureSpace (ℕ → Bool) :=
  ⟨Measure.infinitePi fun _ => fairCoin⟩

attribute [local instance] coinSpace

/-- The coin-to-sign map: `true ↦ 1`, `false ↦ -1`. -/
def boolSign (b : Bool) : ℂ := if b then 1 else -1

lemma measurable_boolSign : Measurable boolSign := Measurable.of_discrete

/-- `uniformOn` of a two-point set is the average of the two Dirac masses. -/
lemma uniformOn_pair {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {a b : α} (hab : a ≠ b) :
    ProbabilityTheory.uniformOn ({a, b} : Set α) =
      (2 : ENNReal)⁻¹ • (Measure.dirac a + Measure.dirac b) := by
  have hd : Disjoint ({a} : Set α) ({b} : Set α) := Set.disjoint_singleton.mpr hab
  have hcount : Measure.count ({a, b} : Set α) = 2 := by
    rw [Set.insert_eq, measure_union hd (measurableSet_singleton b),
      Measure.count_singleton, Measure.count_singleton, one_add_one_eq_two]
  unfold ProbabilityTheory.uniformOn ProbabilityTheory.cond
  rw [hcount, Set.insert_eq, Measure.restrict_union hd (measurableSet_singleton b),
    Measure.restrict_singleton, Measure.restrict_singleton,
    Measure.count_singleton, Measure.count_singleton, one_smul, one_smul]

/-- The law of the coin sign is uniform on `{-1, 1}` w.r.t. counting measure. -/
lemma map_boolSign_fairCoin :
    Measure.map boolSign fairCoin = ProbabilityTheory.uniformOn ({-1, 1} : Set ℂ) := by
  rw [uniformOn_pair (by norm_num : (-1 : ℂ) ≠ 1), fairCoin,
    Measure.map_smul, Measure.map_add _ _ measurable_boolSign,
    Measure.map_dirac measurable_boolSign false, Measure.map_dirac measurable_boolSign true]
  rfl

/-- An honest Rademacher coefficient sequence inhabits the counting-measure structure. -/
noncomputable def coinKacCoefficients :
    KacCoefficients ({-1, 1} : Set ℂ) (ℕ → Bool) Measure.count where
  toFun i ω := boolSign (ω i)
  h_indep :=
    ProbabilityTheory.iIndepFun_infinitePi (P := fun _ => fairCoin)
      (X := fun _ : ℕ => boolSign) (fun _ => measurable_boolSign)
  h_unif i := by
    show Measure.map (fun ω : ℕ → Bool => boolSign (ω i)) ℙ =
      ProbabilityTheory.cond Measure.count ({-1, 1} : Set ℂ)
    have h1 : (fun ω : ℕ → Bool => boolSign (ω i)) =
        boolSign ∘ (fun ω : ℕ → Bool => ω i) := rfl
    have h2 : Measure.map (fun ω : ℕ → Bool => ω i) ℙ = fairCoin :=
      Measure.infinitePi_map_eval (fun _ => fairCoin) i
    rw [h1, ← Measure.map_map measurable_boolSign (measurable_pi_apply i), h2,
      map_boolSign_fairCoin]
    rfl

/-- The structure with `μ := Measure.count` is non-vacuous. -/
theorem kacCoefficients_count_nonempty :
    Nonempty (KacCoefficients ({-1, 1} : Set ℂ) (ℕ → Bool) Measure.count) :=
  ⟨coinKacCoefficients⟩

end RegressionWitness

/--
Let $f(z)=\sum_{0\leq k\leq n} \epsilon_k z^k$ be a random polynomial, where
$\epsilon_k\in \{-1,1\}$ independently uniformly at random for $0\leq k\leq n$.

Is it true that, if $R_n$ is the number of roots of $f(z)$ in
$\{ z\in \mathbb{C} : \lvert z\rvert \leq 1\}$, then
$$
  \frac{R_n}{n/2}\to 1
$$
almost surely?

There is some ambiguity as to whether the intended coefficient set is $\{-1, 1\}$ or $\{0, 1\}$,
see `erdos_522.variants.zero_one` for the alternate version.
-/
@[category research open, AMS 12 60]
theorem erdos_522 :
    answer(sorry) ↔ ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (c : KacCoefficients ({-1, 1} : Set ℂ) Ω Measure.count),
      ℙ {ω | atTop.Tendsto (fun n : ℕ ↦ (2 * c.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1)} = 1 := by
  sorry

/--
Let $f(z)=\sum_{0\leq k\leq n} \epsilon_k z^k$ be a random polynomial, where
$\epsilon_k\in \{0,1\}$ independently uniformly at random for $0\leq k\leq n$.

Is it true that, if $R_n$ is the number of roots of $f(z)$ in
$\{ z\in \mathbb{C} : \lvert z\rvert \leq 1\}$, then
$$
  \frac{R_n}{n/2}\to 1
$$
almost surely?
-/
@[category research open, AMS 12 60]
theorem erdos_522.variants.zero_one :
    answer(sorry) ↔ ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {n : ℕ} (hn : 1 ≤ n) (f : KacCoefficients ({0, 1} : Set ℂ) Ω Measure.count),
      ℙ {ω | atTop.Tendsto (fun n : ℕ ↦ (2 * f.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1)} = 1 := by
  sorry

/--
Erdős and Offord showed that the number of real roots of a random degree `n` polynomial with `±1`
coefficients is `(2/π+o(1))log n`.
-/
@[category research solved, AMS 12 60]
theorem erdos_522.variants.number_real_roots : ∃ p o : ℕ → ℝ,
    atTop.Tendsto o (𝓝 0) ∧ atTop.Tendsto p (𝓝 0) ∧
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (n : ℕ) (hn : 2 ≤ n) (f : KacCoefficients ({-1, 1} : Set ℝ) Ω Measure.count),
      (ℙ {ω | |(f.roots n ω).card / (n : ℝ).log - 2 / π| ≥ o n}).toReal ≤ p n := by
  sorry

/--
Yakir proved that almost all Kac polynomials have `n/2+O(n^(9/10))` many roots in `{z∈C:|z|≤1}`.
-/
@[category research solved, AMS 12 60]
theorem erdos_522.variants.yakir_solution :
    ∃ p : ℕ → ℝ, atTop.Tendsto p (𝓝 0) ∧
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (n : ℕ) (hn : 2 ≤ n) (f : KacCoefficients ({-1, 1} : Set ℂ) Ω Measure.count),
       (ℙ {ω | |(f.roots n ω).countP
         (· ∈ Metric.closedBall 0 1) - (n / 2 : ℝ)| ≥ n^(9/10 : ℝ) }).toReal ≤ p n := by
  sorry

end Erdos522
