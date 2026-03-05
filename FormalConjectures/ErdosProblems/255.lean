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
# Erdős Problem 255

For any infinite sequence in [0,1], must there exist a sub-interval whose discrepancy is
unbounded?

*Reference:* [erdosproblems.com/255](https://www.erdosproblems.com/255)

[Sc68] Schmidt, W.M., _Irregularities of distribution. VII_. Acta Arith. 21 (1972), 45-50.
-/

open Finset Classical

namespace Erdos255

/--
The discrepancy of a sequence $z : \mathbb{N} \to \mathbb{R}$ at length $N$ with respect to
a sub-interval $[a, b] \subseteq [0, 1]$:
$$D_N([a,b]) = \#\{n < N : z(n) \in [a, b]\} - N \cdot (b - a)$$
-/
noncomputable def discrepancy (z : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  (((range N).filter (fun n => a ≤ z n ∧ z n ≤ b)).card : ℝ) - (N : ℝ) * (b - a)

/--
Erdős Problem #255 (proved by Schmidt [Sc68]):

Let $z_1, z_2, \ldots \in [0,1]$ be an infinite sequence. Define the discrepancy
$$D_N(I) = \#\{n \leq N : z_n \in I\} - N \cdot |I|.$$
Then there must exist some interval $I \subseteq [0,1]$ such that
$$\limsup_{N \to \infty} |D_N(I)| = \infty.$$

Equivalently: for any sequence in $[0,1]$, there exists a sub-interval
$[a,b] \subseteq [0,1]$ such that $|D_N([a,b])|$ is unbounded as $N \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_255 : answer(True) ↔
    ∀ z : ℕ → ℝ,
    (∀ n, 0 ≤ z n ∧ z n ≤ 1) →
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      ∀ M : ℝ, ∃ N : ℕ, |discrepancy z a b N| ≥ M := by
  sorry

end Erdos255
