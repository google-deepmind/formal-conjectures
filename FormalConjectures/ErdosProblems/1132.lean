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
# Erdős Problem 1132

*Reference:* [erdosproblems.com/1132](https://www.erdosproblems.com/1132)

For $x_1, \ldots, x_n \in [-1,1]$, define the Lagrange basis polynomials
$$
  \ell_k(x) = \prod_{i \neq k} \frac{x - x_i}{x_k - x_i},
$$
so that $\ell_k(x_k) = 1$ and $\ell_k(x_i) = 0$ for $i \neq k$.

Let $x_1, x_2, \ldots \in [-1,1]$ be an infinite sequence, and let
$$
  L_n(x) = \sum_{1 \leq k \leq n} |\ell_k(x)|,
$$
where each $\ell_k(x)$ is defined with respect to $x_1, \ldots, x_n$.

[Be31] Bernstein proved that the set of $x \in (-1,1)$ for which the limsup
condition (Part 2) holds is everywhere dense.
-/

open Finset BigOperators Filter MeasureTheory

namespace Erdos1132

/-- The Lagrange basis polynomial $\ell_k(x)$ for nodes indexed by $\operatorname{Fin} n$.
$\ell_k(x) = \prod_{i \neq k} \frac{x - x_i}{x_k - x_i}$ -/
noncomputable def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: $L_n(x) = \sum_k |\ell_k(x)|$ -/
noncomputable def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- The first $n$ elements of an infinite sequence, viewed as $\operatorname{Fin} n \to \mathbb{R}$. -/
noncomputable def firstN (seq : ℕ → ℝ) (n : ℕ) : Fin n → ℝ := fun i => seq i.val

/-- $L_n(x)$: the Lebesgue function using the first $n$ points of the sequence. -/
noncomputable def L (seq : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  lebesgueFunction (firstN seq n) x

/-- A sequence is valid for interpolation: values in $[-1,1]$ and pairwise distinct. -/
def ValidSeq (seq : ℕ → ℝ) : Prop :=
  Function.Injective seq ∧ ∀ i, seq i ∈ Set.Icc (-1 : ℝ) 1

/--
Erdős Problem 1132 (Part 1):

For any infinite sequence $x_1, x_2, \ldots \in [-1,1]$ of distinct points, must there
exist $x \in (-1,1)$ and a constant $C$ such that $L_n(x) > \frac{2}{\pi} \log n - C$ for
infinitely many $n$?
-/
@[category research open, AMS 26 41]
theorem erdos_1132 : answer(sorry) ↔
    ∀ (seq : ℕ → ℝ), ValidSeq seq →
      ∃ x ∈ Set.Ioo (-1 : ℝ) 1, ∃ C : ℝ,
        ∃ᶠ n in atTop,
          L seq n x > (2 / Real.pi) * Real.log (n : ℝ) - C := by
  sorry

/--
Erdős Problem 1132 (Part 2):

For any infinite sequence $x_1, x_2, \ldots \in [-1,1]$ of distinct points, is it true that
$\limsup_{n \to \infty} L_n(x) / \log n \geq \frac{2}{\pi}$
for almost all $x \in (-1,1)$?

Bernstein [Be31] proved that the set of $x \in (-1,1)$ for which the limsup
condition holds is everywhere dense.
-/
@[category research open, AMS 26 41]
theorem erdos_1132.variants.part2 : answer(sorry) ↔
    ∀ (seq : ℕ → ℝ), ValidSeq seq →
      ∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)),
        Filter.limsup (fun n => L seq n x / Real.log (n : ℝ)) atTop ≥ 2 / Real.pi := by
  sorry

end Erdos1132
