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
# Erdős Problem 1131

*Reference:* [erdosproblems.com/1131](https://www.erdosproblems.com/1131)

For $x_1, \ldots, x_n \in [-1,1]$, define the Lagrange basis polynomials
$$\ell_k(x) = \prod_{i \neq k} \frac{x - x_i}{x_k - x_i},$$
so that $\ell_k(x_k) = 1$ and $\ell_k(x_i) = 0$ for $i \neq k$.

What is the minimal value of
$$I(x_1, \ldots, x_n) = \int_{-1}^{1} \sum_k |\ell_k(x)|^2 \, dx?$$

In particular, is it true that $\min I = 2 - (1 + o(1)) / n$?

Fejér [Fe32] showed that the roots of the integral of the Legendre polynomial
minimize $\max_{x \in [-1,1]} \sum_k |\ell_k(x)|^2$. Erdős [Er61] conjectured
that these nodes also minimize the $L^2$ functional $I$, but Szabados [Sz66]
disproved this for all $n > 3$.

[ESVV94] Erdős, P., Szabados, J., Varma, A.K., and Vértesi, P.,
_On an interpolation theoretical extremal problem_.
Studia Sci. Math. Hungar. (1994), 55–60. Proved that
$2 - O((\log n)^2 / n) \le \min I \le 2 - 2/(2n-1)$,
where the upper bound is witnessed by the roots of the integral of the
Legendre polynomial.

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
6 (1961), p. 221.

[Fe32] Fejér, L., _Bestimmung derjenigen Abszissen eines Intervalles, für welche die
Quadratsumme der Grundfunktionen der Lagrangeschen Interpolation im Intervalle ein
möglichst kleines Maximum besitzt_. Ann. Scuola Norm. Sup. Pisa Cl. Sci. (2) (1932),
263–276.

[Sz66] Szabados, J., _On a problem of P. Erdős_. Acta Math. Acad. Sci. Hungar.
(1966), 155–157.
-/

open MeasureTheory Finset Filter BigOperators

namespace Erdos1131

/-- The Lagrange basis polynomial $\ell_k(x)$ for nodes `nodes : Fin n → ℝ` at index $k$:
$$\ell_k(x) = \prod_{i \neq k} \frac{x - x_i}{x_k - x_i}.$$ -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The $L^2$ functional $I(x_1, \ldots, x_n) = \int_{-1}^{1} \sum_k \ell_k(x)^2 \, dx$. -/
noncomputable def lagrangeL2 {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, ∑ k : Fin n, lagrangeBasis nodes k x ^ 2

/-- The minimum of the $L^2$ functional over all choices of $n$ distinct nodes in $[-1, 1]$.
The nodes are required to be distinct (`Function.Injective nodes`) so that the
Lagrange basis polynomials are well-defined. -/
noncomputable def minLagrangeL2 (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ nodes : Fin n → ℝ,
    Function.Injective nodes ∧
    (∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1) ∧
    v = lagrangeL2 nodes}

/--
Erdős Problem 1131: For $x_1, \ldots, x_n \in [-1,1]$, let
$\ell_k(x) = \prod_{i \neq k} (x - x_i)/(x_k - x_i)$ be the Lagrange basis polynomials.
The conjecture asks whether the minimum of
$I(x_1, \ldots, x_n) = \int_{-1}^{1} \sum_k |\ell_k(x)|^2 \, dx$ satisfies
$\min I = 2 - (1 + o(1))/n$, i.e., $n \cdot (2 - \min I) \to 1$ as $n \to \infty$.

See [ESVV94] for the best known bounds.
-/
@[category research open, AMS 41]
theorem erdos_1131 :
    answer(sorry) ↔
    Tendsto (fun n : ℕ => (n : ℝ) * (2 - minLagrangeL2 n)) atTop (nhds 1) := by
  sorry

end Erdos1131
