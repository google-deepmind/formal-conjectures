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
# Erdős Problem 161

Erdős conjectured that for $t$-uniform hypergraph 2-colourings, the balanced-colouring threshold
$F^{(t)}(n,\alpha)$ grows polynomially in $\log n$ for any $\alpha > 0$, in contrast with the
iterated-logarithm growth at $\alpha = 0$.

*Reference:* [erdosproblems.com/161](https://www.erdosproblems.com/161)

[Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and
differences_. Mathematics of Ramsey theory, Algorithms Combin. 5 (1990), 12-28.

[CFS11] Conlon, D., Fox, J., and Sudakov, B., _An approximate version of Sidorenko's
conjecture_. Geometric and Functional Analysis 20 (2010), 1354-1366.
-/

open Finset Real

namespace Erdos161

/-- A 2-colouring $c$ of the $t$-element subsets of $\text{Fin}(n)$ is $\alpha$-balanced at
threshold $m$ if for every subset $X \subseteq \text{Fin}(n)$ with $|X| \geq m$, each colour class
contains at least $\alpha \binom{|X|}{t}$ many $t$-element subsets of $X$. -/
def IsBalancedColouring (n t m : ℕ) (α : ℝ) (c : Finset (Fin n) → Bool) : Prop :=
  ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool,
      α * (Nat.choose X.card t : ℝ) ≤
        (((X.powersetCard t).filter (fun S => c S = b)).card : ℝ)

/-- $F^{(t)}(n, \alpha)$ is the smallest $m$ such that there exists a 2-colouring of the
$t$-element subsets of $[n]$ that is $\alpha$-balanced at threshold $m$. -/
noncomputable def fBalanced (t n : ℕ) (α : ℝ) : ℕ :=
  sInf { m : ℕ | ∃ c : Finset (Fin n) → Bool, IsBalancedColouring n t m α c }

/--
Erdős Conjecture (Problem 161) [Er90b, p.21]:

For any $t \geq 2$ and $0 < \alpha < 1/2$, the function $F^{(t)}(n, \alpha)$ is bounded by a
polynomial in $\log n$. Specifically, there exist constants $C > 0$ and $D > 0$
(depending on $t$ and $\alpha$) such that $F^{(t)}(n, \alpha) \leq C \cdot (\log n)^D$ for all
sufficiently large $n$.

This captures Erdős's conjecture that "the jump occurs all in one step at $0$":
for $\alpha > 0$, $F^{(t)}(n, \alpha)$ grows polynomially in $\log n$, contrasting with the
much slower iterated-logarithm growth $F^{(t)}(n, 0) \approx \log_{t-1}(n)$.
-/
@[category research open, AMS 5]
theorem erdos_161 :
    ∀ t : ℕ, 2 ≤ t →
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧
    ∃ D : ℝ, 0 < D ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (fBalanced t n α : ℝ) ≤ C * (Real.log (n : ℝ)) ^ D := by
  sorry

end Erdos161
