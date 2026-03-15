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
# Erdős Problem 162

For a 2-colouring of the edges of $K_n$, let $F(n, \alpha)$ be the smallest $m$ such that every
subset of size at least $m$ has both colour classes containing more than an $\alpha$ fraction of its
edges. Erdős conjectured that $F(n, \alpha) \sim c_\alpha \log n$ for a constant $c_\alpha > 0$.

*Reference:* [erdosproblems.com/162](https://www.erdosproblems.com/162)

[Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and differences_.
Mathematics of Ramsey theory, Algorithms and Combinatorics, 5 (1990), Springer, Berlin, 12-28.
-/

open Finset Real

namespace Erdos162

/-- A 2-colouring $c$ of the edges (2-element subsets) of $\operatorname{Fin}(n)$ is
$\alpha$-balanced at threshold $m$ if for every subset $X \subseteq \operatorname{Fin}(n)$
with $|X| \geq m$, each colour class contains more than $\alpha \binom{|X|}{2}$
edges within $X$. -/
def IsEdgeBalanced (n m : ℕ) (α : ℝ) (c : Finset (Fin n) → Bool) : Prop :=
  ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool,
      α * (Nat.choose X.card 2 : ℝ) <
        (((X.powersetCard 2).filter (fun S => c S = b)).card : ℝ)

/-- $F(n, \alpha)$ is the smallest threshold $m$ such that there exists a 2-colouring
of the edges of $K_n$ that is $\alpha$-balanced at threshold $m$. -/
noncomputable def F (n : ℕ) (α : ℝ) : ℕ :=
  sInf { m : ℕ | ∃ c : Finset (Fin n) → Bool, IsEdgeBalanced n m α c }

/--
Erdős Conjecture (Problem 162) [Er90b, p.21]:

For every fixed $0 < \alpha < 1/2$, $F(n, \alpha) \sim c_\alpha \log n$ for some
constant $c_\alpha > 0$. That is, the ratio $F(n, \alpha) / \log n$ converges to a positive
constant $c_\alpha$ as $n \to \infty$.

This sharpens the known bound $F(n, \alpha) = \Theta(\log n)$ (established via the
probabilistic method) to an exact asymptotic with a well-defined constant.
-/
@[category research open, AMS 5]
theorem erdos_162 :
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          (c - ε) * Real.log (n : ℝ) ≤ (F n α : ℝ) ∧
          (F n α : ℝ) ≤ (c + ε) * Real.log (n : ℝ) := by
  sorry

end Erdos162
