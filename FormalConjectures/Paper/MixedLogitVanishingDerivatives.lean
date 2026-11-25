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
# Vanishing derivatives of mixed-logit shares

Bajari, Fox, Kim, and Ryan conjecture that for $A>1$, the function
$g_A(c)=e^c/(A+e^c)$ has a zero derivative at $c=0$ at at most one positive order.
We state the equivalent assertion for the integer polynomials
$P_0(X)=X$ and $P_{n+1}(X)=X(1-X)P_n'(X)$.

`Real.iteratedDeriv_exp_div` proves that $g_A^{(n)}(0)=P_n(1/(1+A))$.
The change of variables $x=1/(1+A)$ maps $A>1$ onto $0<x<1/2$, as proved by
`Real.one_div_one_add_mem_Ioo` and `Real.exists_one_div_one_add_eq`.
The source selects a good with minimum intercept among at least two inside goods.
This gives $A>1$; conversely, every $A>1$ occurs with two equal intercepts
$-\log(A-1)$.

## References

* P. Bajari, J. T. Fox, K. Kim, and S. P. Ryan,
  *The Random Coefficients Logit Model Is Identified*
  ([September 2010 author manuscript](https://hdl.handle.net/1721.1/101264)),
  Appendix A.3, equation (15), footnote 16, printed p. 18 (PDF p. 19).
-/

@[expose] public section

namespace MixedLogitVanishingDerivatives

/-- **Bajari–Fox–Kim–Ryan's vanishing-derivative conjecture.** At any real
$0<x<1/2$, two positive-order sigmoid derivative polynomials can vanish together only if
their orders agree. The endpoint $x=1/2$ is excluded because both $P_2$ and $P_4$ vanish there. -/
@[category research open, AMS 12 26]
theorem unique_vanishing_order (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmx : Polynomial.aeval x (Polynomial.sigmoidDerivPoly m) = 0)
    (hnx : Polynomial.aeval x (Polynomial.sigmoidDerivPoly n) = 0) : m = n := by
  sorry

end MixedLogitVanishingDerivatives
