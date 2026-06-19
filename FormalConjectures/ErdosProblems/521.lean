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
# Erdős Problem 521

Let $(\varepsilon_k)_{k \geq 0}$ be independently uniformly chosen from $\{-1, 1\}$,
and let $R_n$ count the number of real roots of $f_n(z) = \sum_{k=0}^{n} \varepsilon_k z^k$.
Is it true that, almost surely, $\lim_{n \to \infty} R_n / \log n = 2/\pi$?

Erdős and Offord [EO56] showed that the expected number of real roots is
$(2/\pi + o(1)) \log n$. This conjecture, posed by Erdős [Er61, p.252], asks whether
the convergence holds almost surely. Do [Do24] proved the partial result that for
roots restricted to $[-1, 1]$, the limit $R_n[-1,1] / \log n \to 1/\pi$ holds
almost surely.

Note: Erdős's original formulation [Er61, p.252] is ambiguous about whether
the coefficients are from $\{-1, 1\}$ or $\{0, 1\}$. For $\{0, 1\}$ coefficients,
the expected constant is $1/\pi$ rather than $2/\pi$. This formalization uses
$\{-1, 1\}$ (Rademacher), which is the standard modern interpretation.

## References

[EO56] Erdős, P., Offord, A. C., _On the number of real roots of a random algebraic
equation_. Proc. London Math. Soc. (3) **6** (1956), 139–160.

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
**6** (1961), 221–254.

[Do24] Do, Y., _A strong law of large numbers for real roots of random polynomials_.
arXiv:2403.06353 (2024).

*Reference:* [erdosproblems.com/521](https://www.erdosproblems.com/521)
-/

open MeasureTheory ProbabilityTheory Polynomial Filter Finset

open scoped BigOperators

namespace Erdos521

/-- The polynomial with prescribed $\pm 1$ coefficients:
$f_n(z) = \sum_{k=0}^{n} \varepsilon(k) \cdot z^k$. -/
noncomputable def signPoly (ε : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range (n + 1), C (ε k) * X ^ k

/-- The number of distinct real roots of a real polynomial. -/
noncomputable def numRealRoots (p : Polynomial ℝ) : ℕ :=
  Set.ncard {x : ℝ | p.IsRoot x}

/-- A random variable is Rademacher distributed: it takes values in $\{-1, 1\}$
with equal probability (each with probability $1/2$ on a probability space). -/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 1 ∨ X ω = -1) ∧
  μ {ω | X ω = 1} = μ {ω | X ω = -1}

/--
Erdős Problem 521 [Er61, p.252]:
Let $(\varepsilon_k)_{k \geq 0}$ be independently uniformly chosen at random from $\{-1, 1\}$.
If $R_n$ counts the number of real roots of $f_n(z) = \sum_{k=0}^{n} \varepsilon_k z^k$,
then, almost surely, $\lim_{n \to \infty} R_n / \log n = 2/\pi$.

Erdős and Offord [EO56] showed that the expected number of real roots is
$(2/\pi + o(1)) \log n$. This conjecture asks whether the convergence holds
almost surely.
-/
@[category research open, AMS 12 60]
theorem erdos_521 : answer(sorry) ↔
    ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {ε : ℕ → Ω → ℝ},
    (∀ k, IsRademacher μ (ε k)) →
    iIndepFun ε μ →
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (numRealRoots (signPoly (fun k => ε k ω) n) : ℝ) / Real.log (n : ℝ))
      atTop (nhds (2 / Real.pi)) := by
  sorry

/-- The number of distinct real roots of a real polynomial in a given interval $[a, b]$. -/
noncomputable def numRealRootsIn (p : Polynomial ℝ) (a b : ℝ) : ℕ :=
  Set.ncard {x : ℝ | p.IsRoot x ∧ a ≤ x ∧ x ≤ b}

/--
Do's partial result [Do24]: For random $\pm 1$ polynomials, the number of real roots
in $[-1, 1]$ satisfies $R_n[-1,1] / \log n \to 1/\pi$ almost surely.
This is a partial result towards Erdős Problem 521, resolving the conjecture
for roots restricted to $[-1, 1]$.
-/
@[category research solved, AMS 12 60]
theorem erdos_521.variants.do_restricted_roots :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {ε : ℕ → Ω → ℝ},
    (∀ k, IsRademacher μ (ε k)) →
    iIndepFun ε μ →
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (numRealRootsIn (signPoly (fun k => ε k ω) n) (-1) 1 : ℝ) / Real.log (n : ℝ))
      atTop (nhds (1 / Real.pi)) := by
  sorry

/--
Erdős–Offord expectation result [EO56]: The expected number of real roots of a
random degree $n$ polynomial with $\pm 1$ coefficients satisfies
$\mathbb{E}[R_n] / \log n \to 2/\pi$.
This is the convergence in expectation that motivates the almost sure conjecture
(Erdős Problem 521).
-/
@[category research solved, AMS 12 60]
theorem erdos_521.variants.erdos_offord_expectation :
    ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {ε : ℕ → Ω → ℝ},
    (∀ k, IsRademacher μ (ε k)) →
    iIndepFun ε μ →
    Tendsto
      (fun n => (∫ ω, (numRealRoots (signPoly (fun k => ε k ω) n) : ℝ) ∂μ) / Real.log (n : ℝ))
      atTop (nhds (2 / Real.pi)) := by
  sorry

/-- A random variable is Bernoulli(1/2) distributed: it takes values in $\{0, 1\}$
with equal probability. -/
def IsBernoulliHalf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  (∀ ω, X ω = 0 ∨ X ω = 1) ∧
  μ {ω | X ω = 0} = μ {ω | X ω = 1}

/--
$\{0, 1\}$ coefficient variant: Erdős's original formulation [Er61, p.252] may have
intended coefficients from $\{0, 1\}$ instead of $\{-1, 1\}$. For $\{0, 1\}$ coefficients,
the expected constant is $1/\pi$ rather than $2/\pi$.
-/
@[category research open, AMS 12 60]
theorem erdos_521.variants.zero_one_coefficients : answer(sorry) ↔
    ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {ε : ℕ → Ω → ℝ},
    (∀ k, IsBernoulliHalf μ (ε k)) →
    iIndepFun ε μ →
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (numRealRoots (signPoly (fun k => ε k ω) n) : ℝ) / Real.log (n : ℝ))
      atTop (nhds (1 / Real.pi)) := by
  sorry

end Erdos521
