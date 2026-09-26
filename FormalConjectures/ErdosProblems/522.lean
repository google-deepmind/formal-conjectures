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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 522

*References:*
- [erdosproblems.com/522](https://www.erdosproblems.com/522)
- [Ka26] Kawada, S., *Almost-Sure Radial Laws for Nested Random Polynomials and Erdős
  Problem #522*, [doi:10.5281/zenodo.22970145](https://doi.org/10.5281/zenodo.22970145) (2026).
  Lean 4 formalization: [chreia/erdos-522](https://github.com/chreia/erdos-522/tree/b3c1d7c089fcada59cc48cf664cd3d02157407ca),
  v1.0.0.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real

namespace Erdos522

/--
A sequence of *Kac coefficients* over a subset `S` of a field `k` is a countably infinite sequence
of independent random variables, each uniformly distributed over `S` with respect to the reference
measure `μ`. The default reference measure is the counting measure, so that for a finite set `S`
each coefficient takes every value of `S` with probability `1 / |S|`.

Such a sequence determines a *Kac polynomial* of degree `n` for each `n`, which is the random
polynomial given by `KacCoefficients.polynomial`.
-/
@[ext]
structure KacCoefficients
    {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count) where
  toFun : ℕ → Ω → k
  h_indep : ProbabilityTheory.iIndepFun toFun ℙ
  h_unif : ∀ i, MeasureTheory.pdf.IsUniform (toFun i) S ℙ μ

variable {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count)

/--
We can always view a Kac polynomial as a random variable on `ℕ`.
-/
instance : FunLike (KacCoefficients S Ω μ) ℕ (Ω → k) where
  coe P := P.toFun
  coe_injective P Q h := by aesop

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
    (ω : Ω) : ℕ :=
  open scoped Classical in
  (c.roots n ω).countP (· ∈ Metric.closedBall 0 1)

end KacCoefficients

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

This is true. A Lean proof is given in [Ka26]. One linked theorem, from v1.0.0 of the
formalization, proves $R_n / n \to 1/2$ almost surely for independent uniform signs on an
arbitrary probability space. The other linked file copies the definitions of this file and
derives the statement below from that theorem.
-/
@[category research solved, AMS 12 60,
  formal_proof using lean4 at "https://github.com/chreia/erdos-522/blob/b3c1d7c089fcada59cc48cf664cd3d02157407ca/lean/Erdos522/Probability/IndependentCoefficientRadialLaws.lean#L39-L47",
  formal_proof using lean4 at "https://github.com/chreia/erdos-522/blob/57af1556d1b40f37d09d1270495acc0f282ff0fc/lean/Erdos522/Bridge/FormalConjectures.lean#L238-L253"]
theorem erdos_522 :
    answer(True) ↔ ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (c : KacCoefficients ({-1, 1} : Set ℂ) Ω),
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
      {n : ℕ} (hn : 1 ≤ n) (f : KacCoefficients ({0, 1} : Set ℂ) Ω),
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
      (n : ℕ) (hn : 2 ≤ n) (f : KacCoefficients ({-1, 1} : Set ℝ) Ω),
      (ℙ {ω | |(f.roots n ω).card / (n : ℝ).log - 2 / π| ≥ o n}).toReal ≤ p n := by
  sorry

open scoped Classical in
/--
Yakir proved that almost all Kac polynomials have `n/2+O(n^(9/10))` many roots in `{z∈C:|z|≤1}`.
-/
@[category research solved, AMS 12 60]
theorem erdos_522.variants.yakir_solution :
    ∃ p : ℕ → ℝ, atTop.Tendsto p (𝓝 0) ∧
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (n : ℕ) (hn : 2 ≤ n) (f : KacCoefficients ({-1, 1} : Set ℂ) Ω),
       (ℙ {ω | |(f.roots n ω).countP
         (· ∈ Metric.closedBall 0 1) - (n / 2 : ℝ)| ≥ n^(9/10 : ℝ) }).toReal ≤ p n := by
  sorry

end Erdos522
