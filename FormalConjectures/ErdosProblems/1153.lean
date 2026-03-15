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
# Erdős Problem 1153

*Reference:* [erdosproblems.com/1153](https://www.erdosproblems.com/1153)

For $x_1, \ldots, x_n \in [-1,1]$, define the Lagrange basis polynomials
$$\ell_k(x) = \prod_{i \neq k} \frac{x - x_i}{x_k - x_i},$$
so that $\ell_k(x_k) = 1$ and $\ell_k(x_i) = 0$ for $i \neq k$.

Let $\lambda(x) = \sum_k |\ell_k(x)|$ (the Lebesgue function).

Is it true that, for any fixed $-1 \leq a < b \leq 1$,
$$\max_{x \in [a,b]} \lambda(x) > \left(\frac{2}{\pi} - o(1)\right) \log n?$$

Bernstein [Be31] proved this for $a = -1$ and $b = 1$, and Erdős [Er61c] improved this to
$\max_{x \in [-1,1]} \lambda(x) > \frac{2}{\pi} \log n - O(1)$.
This is best possible, since taking the $x_i$ as the roots of the $n$th Chebyshev
polynomial yields $\max_{x \in [-1,1]} \lambda(x) < \frac{2}{\pi} \log n + O(1)$.

The conjecture asks whether the same lower bound (up to $o(1)$ in the coefficient)
holds when the maximum is restricted to any subinterval $[a,b] \subseteq [-1,1]$.

See also related problems [#1129](https://www.erdosproblems.com/1129) and
[#1132](https://www.erdosproblems.com/1132).

[Er61c] Erdős, P., _Problems and results on the theory of interpolation. II_,
  Acta Math. Acad. Sci. Hungar. (1961), 235–244.

[Be31] Bernstein, S., _Sur la limitation des valeurs d'un polynome $P_n(x)$ de degré $n$ sur
  tout un segment par ses valeurs en $(n+1)$ points du segment_, Izv. Akad. Nauk. SSSR (1931),
  1025–1050.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999), §2.44.
-/

open Finset BigOperators Set

namespace Erdos1153

/-- The Lagrange basis polynomial $\ell_k(x)$ for nodes indexed by $\mathrm{Fin}\, n$.
$\ell_k(x) = \prod_{i \neq k} (x - x_i) / (x_k - x_i)$. -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.erase k, (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: $\lambda(x) = \sum_k |\ell_k(x)|$. -/
noncomputable def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/--
Erdős Problem 1153:

For any fixed $-1 \leq a < b \leq 1$ and any $\varepsilon > 0$, there exists $N$ such that
for all $n \geq N$, for any choice of $n$ distinct nodes $x_1, \ldots, x_n \in [-1,1]$,
$$\max_{x \in [a,b]} \sum_k |\ell_k(x)| > \left(\frac{2}{\pi} - \varepsilon\right) \log n.$$
-/
@[category research solved, AMS 41]
theorem erdos_1153 : answer(True) ↔
    ∀ a b : ℝ, a < b → -1 ≤ a → b ≤ 1 →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ nodes : Fin n → ℝ,
            Function.Injective nodes →
            (∀ i, nodes i ∈ Icc (-1 : ℝ) 1) →
            ∃ x ∈ Icc a b,
              lebesgueFunction nodes x > (2 / Real.pi - ε) * Real.log (n : ℝ) := by
  sorry

end Erdos1153
