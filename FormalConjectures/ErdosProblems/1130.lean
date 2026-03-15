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
# Erdős Problem 1130

For nodes $x_1, \ldots, x_n \in [-1,1]$, consider the Lebesgue function
$\Lambda(x) = \sum_k |\ell_k(x)|$ of Lagrange interpolation, where $\ell_k$
are the Lagrange basis polynomials. Partition $[-1,1]$ by $-1 = x_0 < x_1
< \cdots < x_n < x_{n+1} = 1$ and let $\Upsilon(x_1, \ldots, x_n)$ be the
minimum over subintervals of the maximum of $\Lambda$. The conjecture asks
whether $\Upsilon(x_1, \ldots, x_n) \ll \log n$.

*Reference:* [erdosproblems.com/1130](https://www.erdosproblems.com/1130)

[Er47] Erdős, P., _Some remarks on polynomials_. Bull. Amer. Math. Soc. (1947),
1169-1176.

[dBPi78] de Boor, C. and Pinkus, A., _Proof of the conjectures of Bernstein
and Erdős concerning the optimal nodes for polynomial interpolation_,
J. Approx. Theory (1978), 289-303.
-/

open Finset

open scoped BigOperators

namespace Erdos1130

/-- The Lagrange basis polynomial $\ell_k(x)$ for nodes indexed by `Fin n`.
$$\ell_k(x) = \prod_{i \neq k} \frac{x - x_i}{x_k - x_i}$$ -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: $\Lambda(x) = \sum_k |\ell_k(x)|$ -/
noncomputable def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- Nodes are valid: strictly increasing and in $[-1, 1]$. -/
def ValidNodes {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  StrictMono nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

/-- The boundary sequence: $-1$, then the $n$ nodes in order, then $1$,
giving $n + 2$ points partitioning $[-1, 1]$ into $n + 1$ subintervals. -/
noncomputable def boundary {n : ℕ} (nodes : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  fun i =>
    if h₁ : i.val = 0 then -1
    else if h₂ : i.val ≤ n then nodes ⟨i.val - 1, by omega⟩
    else 1

/-- The supremum of the Lebesgue function on the $i$-th subinterval
$[\text{boundary}(i), \text{boundary}(i+1)]$. -/
noncomputable def localMax {n : ℕ} (nodes : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  sSup ((lebesgueFunction nodes) ''
    (Set.Icc (boundary nodes ⟨i.val, by omega⟩)
             (boundary nodes ⟨i.val + 1, by omega⟩)))

/--
Proved by de Boor and Pinkus [dBPi78].

For $x_1, \ldots, x_n \in [-1,1]$, let
$\ell_k(x) = \prod_{i \neq k} (x - x_i)/(x_k - x_i)$ be the Lagrange basis
polynomials (fundamental functions of Lagrange interpolation), satisfying
$\ell_k(x_k) = 1$ and $\ell_k(x_i) = 0$ for $i \neq k$.

Set $x_0 = -1$ and $x_{n+1} = 1$. Define
$$\Upsilon(x_1, \ldots, x_n) = \min_{0 \le i \le n} \max_{x \in [x_i, x_{i+1}]} \sum_k |\ell_k(x)|.$$

The conjecture asks: is $\Upsilon(x_1, \ldots, x_n) \ll \log n$?

This is true. It follows from the equioscillation result (Erdős Problem 1129)
and the work of de Boor and Pinkus that
$\Upsilon(x_1, \ldots, x_n) \le \frac{2}{\pi} \log n + O(1)$.
-/
@[category research solved, AMS 41]
theorem erdos_1130 : answer(True) ↔
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ), n ≥ 2 →
    ∀ (nodes : Fin n → ℝ), ValidNodes nodes →
    ∃ i : Fin (n + 1), localMax nodes i ≤ C * Real.log n := by
  sorry

end Erdos1130
