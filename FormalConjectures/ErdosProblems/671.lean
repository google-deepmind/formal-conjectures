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
# Erdős Problem 671

*Reference:* [erdosproblems.com/671](https://www.erdosproblems.com/671)

Given nodes $a_i^n \in [-1,1]$ for $1 \leq i \leq n$, define $p_i^n$ as the
Lagrange basis polynomial of degree $n-1$ (satisfying $p_i^n(a_i^n) = 1$ and
$p_i^n(a_j^n) = 0$ for $j \neq i$) and the Lagrange interpolation operator
$$\mathcal{L}^n f(x) = \sum_i f(a_i^n) p_i^n(x).$$

Part 1: Is there a triangular array of nodes in $[-1,1]$ such that for every
continuous $f: [-1,1] \to \mathbb{R}$ there exists $x \in [-1,1]$ where the
Lebesgue function $\sum_i |p_i^n(x)|$ has infinite limsup yet
$\mathcal{L}^n f(x) \to f(x)$?

Part 2: Is there such an array where the Lebesgue function has infinite limsup
for every $x \in [-1,1]$ and yet for every continuous $f$ there exists $x$ with
$\mathcal{L}^n f(x) \to f(x)$?
-/

open scoped BigOperators

open Filter Set Finset

namespace Erdos671

/-- The value of the $i$-th Lagrange basis polynomial for nodes $a$ at point $x$.
This is $\prod_{j \neq i} (x - a_j) / (a_i - a_j)$. -/
noncomputable def lagrangeBasisEval {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  ∏ j ∈ univ.erase i, (x - a j) / (a i - a j)

/-- The Lebesgue function: $\Lambda_n(x) = \sum_i |p_i^n(x)|$. -/
noncomputable def lebesgueFunction {n : ℕ} (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |lagrangeBasisEval a i x|

/-- The Lagrange interpolation of $f$ at nodes $a$, evaluated at $x$:
$L^n f(x) = \sum_i f(a_i) \cdot p_i(x)$. -/
noncomputable def lagrangeInterpolation {n : ℕ} (a : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, f (a i) * lagrangeBasisEval a i x

/--
Erdős Problem 671 (Part 1): Is there a triangular array of distinct nodes
in $[-1,1]$ such that for every continuous $f : [-1,1] \to \mathbb{R}$, there exists
$x \in [-1,1]$ where the Lebesgue function has infinite limsup yet the Lagrange
interpolation converges to $f(x)$?
-/
@[category research open, AMS 41]
theorem erdos_671 : answer(sorry) ↔
    ∃ (nodes : (n : ℕ) → Fin n → ℝ),
      (∀ n (i : Fin n), nodes n i ∈ Icc (-1 : ℝ) 1) ∧
      (∀ n, Function.Injective (nodes n)) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) →
        ∃ x ∈ Icc (-1 : ℝ) 1,
          (∀ M : ℝ, ∃ᶠ n in atTop, lebesgueFunction (nodes n) x ≥ M) ∧
          Tendsto (fun n => lagrangeInterpolation (nodes n) f x) atTop (nhds (f x)) := by
  sorry

/--
Erdős Problem 671 (Part 2): Is there a triangular array of distinct nodes
in $[-1,1]$ such that the Lebesgue function has infinite limsup at every
$x \in [-1,1]$, and yet for every continuous $f : [-1,1] \to \mathbb{R}$ there
exists $x \in [-1,1]$ where the Lagrange interpolation converges to $f(x)$?
-/
@[category research open, AMS 41]
theorem erdos_671.variants.part2 : answer(sorry) ↔
    ∃ (nodes : (n : ℕ) → Fin n → ℝ),
      (∀ n (i : Fin n), nodes n i ∈ Icc (-1 : ℝ) 1) ∧
      (∀ n, Function.Injective (nodes n)) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ∀ M : ℝ,
        ∃ᶠ n in atTop, lebesgueFunction (nodes n) x ≥ M) ∧
      (∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1) 1) →
        ∃ x ∈ Icc (-1 : ℝ) 1,
          Tendsto (fun n => lagrangeInterpolation (nodes n) f x) atTop (nhds (f x))) := by
  sorry

end Erdos671
