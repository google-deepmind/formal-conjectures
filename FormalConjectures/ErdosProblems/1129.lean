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
# Erdős Problem 1129

Erdős and Bernstein conjectured that the nodes minimising the Lebesgue constant for
Lagrange interpolation on $[-1,1]$ are unique and characterised by equioscillation of
the Lebesgue function. This was proved by Kilgore and de Boor–Pinkus.

*Reference:* [erdosproblems.com/1129](https://www.erdosproblems.com/1129)

[Ki77] Kilgore, T. A., *Optimization of the norm of the Lagrange interpolation operator*,
Bull. Amer. Math. Soc. **83** (1977), 1069-1071.

[KiCh76] Kilgore, T. A. and Cheney, E. W., *A theorem on interpolation in Haar subspaces*,
Aequationes Math. (1976), 391-400.

[dBPi78] de Boor, C. and Pinkus, A., *Proof of the conjectures of Bernstein and Erdős
concerning the optimal nodes for polynomial interpolation*, J. Approx. Theory (1978),
289-303.
-/

open Finset
open scoped BigOperators

namespace Erdos1129

/-- The Lagrange basis polynomial $\ell_k(x)$ for nodes indexed by $\mathrm{Fin}\; n$.
    $\ell_k(x) = \prod_{i \neq k} \frac{x - x_i}{x_k - x_i}$ -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: $L(x) = \sum_k |\ell_k(x)|$ -/
noncomputable def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- The Lebesgue constant: $\Lambda(\mathrm{nodes}) = \sup_{x \in [-1,1]} \sum_k |\ell_k(x)|$ -/
noncomputable def lebesgueConstant {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  sSup ((lebesgueFunction nodes) '' (Set.Icc (-1 : ℝ) 1))

/-- Nodes are valid: strictly increasing and in $[-1, 1]$. -/
def ValidNodes {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  StrictMono nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

/-- The boundary sequence for the equioscillation property: $-1$, then the $n$ nodes
    in order, then $1$, giving $n + 2$ points partitioning $[-1, 1]$ into $n + 1$
    subintervals. -/
noncomputable def boundary {n : ℕ} (nodes : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  fun i =>
    if h₁ : i.val = 0 then -1
    else if h₂ : i.val ≤ n then nodes ⟨i.val - 1, by omega⟩
    else 1

/-- The local maximum of the Lebesgue function on the $i$-th subinterval
    $[b_i, b_{i+1}]$ of the partition induced by the nodes. -/
noncomputable def localMax {n : ℕ} (nodes : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  sSup ((lebesgueFunction nodes) ''
    (Set.Icc (boundary nodes ⟨i.val, by omega⟩)
             (boundary nodes ⟨i.val + 1, by omega⟩)))

/-- The equioscillation property: the local maximum of the Lebesgue function is the
    same on each of the $n + 1$ subintervals $[b_i, b_{i+1}]$. -/
def HasEquioscillation {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  ∀ i j : Fin (n + 1), localMax nodes i = localMax nodes j

/--
Erdős Problem 1129 (Proved by Kilgore [Ki77] and de Boor–Pinkus [dBPi78]):

For $x_1, \ldots, x_n \in [-1,1]$, let
$\ell_k(x) = \prod_{i \neq k} \frac{x - x_i}{x_k - x_i}$
be the Lagrange basis polynomials and
$\Lambda = \max_{x \in [-1,1]} \sum_k |\ell_k(x)|$ the Lebesgue constant.
Erdős and Bernstein conjectured that the minimising nodes are unique
and characterised by the equioscillation property: if
$-1 = x_0 < x_1 < \cdots < x_n < x_{n+1} = 1$ then
$\max_{x \in [x_i, x_{i+1}]} \sum_k |\ell_k(x)|$ is the same for all $0 \leq i \leq n$.

Kilgore proved $\Lambda$ is minimised if and only if equioscillation holds.
De Boor and Pinkus proved the minimising configuration is unique.
-/
@[category research solved, AMS 41]
theorem erdos_1129 (n : ℕ) (hn : 2 ≤ n) :
    ∃ opt : Fin n → ℝ, ValidNodes opt ∧
      -- opt achieves the minimum Lebesgue constant
      (∀ nodes : Fin n → ℝ, ValidNodes nodes →
        lebesgueConstant opt ≤ lebesgueConstant nodes) ∧
      -- the minimiser is unique (among strictly increasing configurations)
      (∀ nodes : Fin n → ℝ, ValidNodes nodes →
        lebesgueConstant nodes = lebesgueConstant opt → nodes = opt) ∧
      -- the minimiser satisfies the equioscillation property
      HasEquioscillation opt ∧
      -- converse: equioscillation characterises the minimiser (Kilgore)
      (∀ nodes : Fin n → ℝ, ValidNodes nodes → HasEquioscillation nodes →
        lebesgueConstant nodes = lebesgueConstant opt) := by
  sorry

end Erdos1129
