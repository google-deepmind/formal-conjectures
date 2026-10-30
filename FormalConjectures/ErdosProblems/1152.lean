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
# Erdős Problem 1152

*References:*
- [erdosproblems.com/1152](https://www.erdosproblems.com/1152)
- [EKS89] Erdős, P., Kroó, A. and Szabados, J., *On convergent interpolatory polynomials*.
  J. Approx. Theory 58 (1989), 232-241. [PDF](https://www.renyi.hu/~p_erdos/1989-16.pdf)
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology Polynomial

namespace Erdos1152

/--
For $n\geq 1$ fix some sequence of $n$ distinct numbers $x_{1n},\ldots,x_{nn}\in [-1,1]$. Let
$\epsilon=\epsilon(n)\to 0$.

Does there always exist a continuous function $f:[-1,1]\to \mathbb{R}$ such that if $p_n$ is a
sequence of polynomials, with degrees $\deg p_n<(1+\epsilon(n))n$, such that
$p_n(x_{kn})=f(x_{kn})$ for all $1\leq k\leq n$, then $p_n(x)\not\to f(x)$ for almost all
$x\in [-1,1]$?

This is Problem 2.42 in [Va99]. The $n$ nodes of the $n$-th row form the finite set `nodes n`.
We take $\epsilon(n)>0$. A smaller $\epsilon$ only shrinks the class of $p_n$, so this is
equivalent to allowing any real $\epsilon(n)\to 0$. We impose the degree bound only for
$n\geq 1$, since for $n=0$ the bound `natDegree < 0` can never hold. We read
"$p_n(x)\not\to f(x)$ for almost all $x$" as: for almost every $x$, the sequence $p_n(x)$ does
not converge to $f(x)$.

For $\deg p_n<n$ the interpolating polynomial is unique (the Lagrange polynomial). Erdős, Kroó
and Szabados [EKS89, pp. 232-233] give necessary and sufficient conditions on the nodes under
which, for every continuous $f$ and every fixed $\epsilon>0$, there are interpolating polynomials
of degree at most $\lfloor n(1+\epsilon)\rfloor$ approximating $f$ at the rate of the best
uniform approximation (in particular converging uniformly to $f$).
-/
@[category research open, question, AMS 41]
theorem erdos_1152 :
    ∀ nodes : ℕ → Finset ℝ, (∀ n, (nodes n).card = n) →
      (∀ n, ∀ x ∈ nodes n, x ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
        ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
          ∀ p : ℕ → ℝ[X],
            (∀ n : ℕ, 1 ≤ n → ((p n).natDegree : ℝ) < (1 + ε n) * n) →
            (∀ n, ∀ x ∈ nodes n, (p n).eval x = f x) →
              ∀ᵐ t ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)),
                ¬ Tendsto (fun n => (p n).eval t) atTop (𝓝 (f t)) := by
  sorry

end Erdos1152
