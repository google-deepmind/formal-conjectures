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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 522

*Reference:* [erdosproblems.com/522](https://www.erdosproblems.com/522)
-/

open MeasureTheory Classical
open scoped ProbabilityTheory Topology Real

namespace Erdos522

/--
A *Kac Polynomial* in `n` coefficients over some subset `S` of a field `k` is a polynomial whose `n`
first coefficients are picked uniformely at random in `S` and whose other coefficients are all `0`.
-/
@[ext]
structure KacPolynomial
    {k : Type*} (n : ℕ) [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := by volume_tac) where
  toFun : Fin n.succ → Ω → k
  h_indep : ProbabilityTheory.iIndepFun toFun ℙ
  h_unif : ∀ i, MeasureTheory.pdf.IsUniform (toFun i) S ℙ μ

variable {k : Type*} (n : ℕ) [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := by volume_tac)

/--
We can always view a Kac polynomial as a random vector
-/
instance : FunLike (KacPolynomial n S Ω μ) (Fin n.succ) (Ω → k) where
  coe P := P.toFun
  coe_injective' := by intro P Q h ; aesop

namespace KacPolynomial

open scoped Polynomial

variable {n S Ω} {μ : Measure k}

/--
The random polynomial associated to a Kac polynomial
-/
noncomputable def toRandomPolynomial (f : KacPolynomial n S Ω μ) :
    Ω → k[X] := fun ω => ∑ i, Polynomial.monomial i.val (f i ω)

/--
The random multiset of roots associated to a Kac polynomial
-/
noncomputable def roots (f : KacPolynomial n S Ω μ) : Ω → Multiset k :=
    fun ω => (f.toRandomPolynomial ω).roots

end KacPolynomial

/--
Let `f(z)=∑_{0≤k≤n} ϵ_k z^k` be a random polynomial, where `ϵ_k∈{−1,1}` independently uniformly at
random for `0≤k≤n`.
Is it true that the number of roots of `f(z)` in `{z∈C:|z|≤1}` is, almost surely, `(1/2+o(1))n`?

Formalization note: here the goal seems to mean that
` ℙ(| #roots of f in unit disk - n/2 | ≥ o(1)) → 0` as `n → ∞`
This is quite awkward to formalise!
-/
@[category research open, AMS 12 60]
theorem erdos_522 :
    answer(sorry) →
      ∃ p o : ℕ → ℝ, Filter.Tendsto o Filter.atTop (𝓝 0) ∧
      Filter.Tendsto p Filter.atTop (𝓝 0) ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
        (n : ℕ) (hn : 1 ≤ n) (f : KacPolynomial n ({-1, 1} : Set ℂ) Ω),
        (ℙ {ω | |(f.roots ω).countP
          (· ∈ Metric.closedBall 0 1) - (n / 2 : ℝ)| ≥ (o n) * n }).toReal ≤ p n := by
  sorry

/--
Erdős and Offord showed that the number of real roots of a random degree `n` polynomial with `±1`
coefficients is `(2/π+o(1))log n`.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/522.lean", AMS 12 60]
theorem erdos_522.variants.number_real_roots : ∃ p o : ℕ → ℝ,
    Filter.Tendsto o Filter.atTop (𝓝 0) ∧ Filter.Tendsto p Filter.atTop (𝓝 0) ∧
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (n : ℕ) (hn : 2 ≤ n) (f : KacPolynomial n ({-1, 1} : Set ℝ) Ω),
      (ℙ {ω | |(f.roots ω).card / (n : ℝ).log - 2 / π| ≥ o n}).toReal ≤ p n := by
  sorry

/--
Yakir proved that almost all Kac polynomials have `n/2+O(n^(9/10))` many roots in `{z∈C:|z|≤1}`.
-/
@[category research formally solved using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/522.lean", AMS 12 60]
theorem erdos_522.variants.yakir_solution :
    ∃ p : ℕ → ℝ, Filter.Tendsto p Filter.atTop (𝓝 0) ∧
    ∀ (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (n : ℕ) (hn : 2 ≤ n) (f : KacPolynomial n ({-1, 1} : Set ℂ) Ω),
       (ℙ {ω | |(f.roots ω).countP
         (· ∈ Metric.closedBall 0 1) - (n / 2 : ℝ)| ≥ n^(9/10 : ℝ) }).toReal ≤ p n := by
  sorry

end Erdos522
