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
# Erdős Problem 227

*References:*
- [erdosproblems.com/227](https://www.erdosproblems.com/227)
- [ClHa64] Clunie, J. and Hayman, W. K., *The maximum term of a power series*.
  J. Analyse Math. **12** (1964), 143–186.
  [DOI](https://doi.org/10.1007/BF02807433)
-/

@[expose] public section

open Filter Topology Polynomial
open Complex (coeff maxTerm maxModulus)

namespace Erdos227

/-- Every entire non-polynomial function has limit $0$ whenever $\mu(r)/M(r)$ converges. -/
def Statement : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → (¬ ∃ p : ℂ[X], ∀ z, f z = p.eval z) →
    ∀ L : ℝ, Tendsto (fun r => maxTerm f r / maxModulus f r) atTop (𝓝 L) → L = 0

/-- Let $f=\sum_{n=0}^\infty a_nz^n$ be an entire function which is not a polynomial.
Is it true that if
$$\lim_{r\to\infty}\frac{\max_n\lvert a_nr^n\rvert}
{\max_{\lvert z\rvert=r}\lvert f(z)\rvert}$$
exists then it must be $0$?

This was disproved in general by Clunie and Hayman [ClHa64], who showed that the limit
can take any value in $[0,1/2]$.
-/
@[category research solved, AMS 30]
theorem erdos_227 : answer(False) ↔ Statement := by
  sorry

/-- For every entire function, any limit of $\mu(r)/M(r)$ lies in $[0,1]$. -/
@[category textbook, AMS 30]
theorem limit_mem_Icc {f : ℂ → ℂ} (hf : Differentiable ℂ f) {L : ℝ}
    (h : Tendsto (fun r => maxTerm f r / maxModulus f r) atTop (𝓝 L)) : L ∈ Set.Icc 0 1 :=
  Complex.limit_mem_Icc hf h

/-- For a nonzero polynomial, $\mu(r)/M(r)$ tends to $1$. -/
@[category textbook, AMS 30]
theorem tendsto_maxTerm_div_maxModulus_polynomial (p : ℂ[X]) (hp : p ≠ 0) :
    Tendsto (fun r => maxTerm (fun z => p.eval z) r / maxModulus (fun z => p.eval z) r)
      atTop (𝓝 1) :=
  Complex.tendsto_maxTerm_div_maxModulus_polynomial p hp

/-- Without the non-polynomial hypothesis, the constant function $1$ gives limit $1$. -/
@[category test, AMS 30]
theorem not_statement_without_nonpolynomial_hypothesis :
    ¬ ∀ f : ℂ → ℂ, Differentiable ℂ f →
      ∀ L : ℝ, Tendsto (fun r => maxTerm f r / maxModulus f r) atTop (𝓝 L) → L = 0 := by
  intro h
  have := h (fun z => (1 : ℂ[X]).eval z) (1 : ℂ[X]).differentiable 1
    (tendsto_maxTerm_div_maxModulus_polynomial 1 one_ne_zero)
  exact one_ne_zero this

end Erdos227
