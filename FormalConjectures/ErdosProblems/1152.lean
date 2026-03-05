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
# Erdős Problem 1152

*Reference:* [erdosproblems.com/1152](https://www.erdosproblems.com/1152)

For $n \geq 1$ fix some sequence of $n$ distinct numbers
$x_{1,n}, \ldots, x_{n,n} \in [-1,1]$. Let $\varepsilon = \varepsilon(n) \to 0$.

Does there always exist a continuous function $f : [-1,1] \to \mathbb{R}$ such that if
$p_n$ is a sequence of polynomials, with degrees $\deg p_n < (1 + \varepsilon(n))n$, such
that $p_n(x_{k,n}) = f(x_{k,n})$ for all $1 \leq k \leq n$, then $p_n(x) \not\to f(x)$
for almost all $x \in [-1,1]$?

Erdős, Kroó, and Szabados [EKS89] proved that if $\varepsilon > 0$ is fixed (does not
$\to 0$), then there exist sequences $x_{i,j}$ such that for any continuous function $f$,
there exists a sequence of polynomials $p_n$ with $\deg p_n < (1+\varepsilon)n$ interpolating
$f$ at $x_{k,n}$, and $p_n(x) \to f(x)$ uniformly for all $x \in [-1,1]$.

[EKS89] Erdős, P., Kroó, A., and Szabados, J., _On convergent interpolatory polynomials_
(1989).

[Va99] Vértesi, P., _Classical (unweighted) and weighted interpolation_ (1999).
-/

open Filter Polynomial MeasureTheory Set

namespace Erdos1152

/--
Erdős Problem 1152 [Va99, 2.42]:

For any triangular array of distinct interpolation nodes in $[-1,1]$ and any function
$\varepsilon(n) \to 0$, there exists a continuous function $f : [-1,1] \to \mathbb{R}$
such that every sequence of polynomials $p_n$ with $\deg p_n < (1 + \varepsilon(n))n$
interpolating $f$ at the nodes fails to converge to $f$ for almost every $x \in [-1,1]$.
-/
@[category research open, AMS 41]
theorem erdos_1152 : answer(sorry) ↔
    ∀ (x : (n : ℕ) → Fin n → ℝ),
      (∀ n, ∀ k : Fin n, x n k ∈ Icc (-1 : ℝ) 1) →
      (∀ n, Function.Injective (x n)) →
      ∀ (ε : ℕ → ℝ),
        (∀ n, 0 < ε n) →
        Tendsto ε atTop (nhds 0) →
        ∃ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) ∧
          ∀ p : ℕ → Polynomial ℝ,
            (∀ n, n ≥ 1 → ((p n).natDegree : ℝ) < (1 + ε n) * n) →
            (∀ n, ∀ k : Fin n, (p n).eval (x n k) = f (x n k)) →
            ∀ᵐ t ∂(volume.restrict (Icc (-1 : ℝ) 1)),
              ¬Tendsto (fun n => (p n).eval t) atTop (nhds (f t)) := by
  sorry

end Erdos1152
