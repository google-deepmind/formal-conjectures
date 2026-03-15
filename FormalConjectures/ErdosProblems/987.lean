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
# Erdős Problem 987

*Reference:* [erdosproblems.com/987](https://www.erdosproblems.com/987)

Let $x_1, x_2, \ldots \in (0,1)$ be an infinite sequence and define
$$A_k = \limsup_{n \to \infty} \left|\sum_{j \leq n} e(k \cdot x_j)\right|$$
where $e(x) = e^{2\pi ix}$.

This is Problem 7.21 in Halberstam and Roth [Ha74], attributed to
Erdős [Er64b][Er65b].

Erdős remarks the analogous statement with $\sup_n$ in place of
$\limsup_n$ is 'easy to see'. Erdős [Er65b] later found a 'very easy'
proof that $A_k \gg \log k$ for infinitely many $k$.
Clunie [Cl67] proved $A_k \gg k^{1/2}$ infinitely often, and showed
there exist sequences with $A_k \leq k$ for all $k$.
Tao has independently found a proof that $A_k \gg k^{1/2}$ infinitely
often. Lindström [Li69] showed that under a finite distinct points
assumption, $A_k \gg k^{1-\varepsilon}$ infinitely often for any
$\varepsilon > 0$; Clunie observed this implies $A_k = \infty$
infinitely often.

[Er64b] Erdős, P., _Problems and results on diophantine approximations_.
Compositio Math. (1964), 52–65.

[Er65b] Erdős, P., _Some recent advances and current problems in number theory_.
Lectures on Modern Mathematics, Vol. III (1965), 196–244.

[Ha74] Halberstam, H. and Roth, K. F., *Sequences*, 1974.

[Cl67] Clunie, J., _On a problem of Erdős_. J. London Math. Soc. (1967), 133–136.

[Li69] Lindström, B., _An inequality for B₂-sequences_. J. Combinatorial Theory
(1969), 211–212.
-/

namespace Erdos987

/-- The exponential sum $S(x, k, n) = \sum_{j < n} e^{2\pi i k x_j}$. -/
noncomputable def exponentialSum (x : ℕ → ℝ) (k : ℕ) (n : ℕ) : ℂ :=
  -- e(k·xⱼ) = e^{2πikxⱼ}
  ∑ j ∈ Finset.range n, Complex.exp (2 * ↑Real.pi * Complex.I * ↑((k : ℝ) * x j))

/--
Erdős Problem 987, Part 1 [Er64b][Er65b]:
For any sequence $x_1, x_2, \ldots \in (0,1)$, $\sup_{k \geq 1} A_k = \infty$ where
$A_k = \limsup_{n \to \infty} \lVert\sum_{j < n} e^{2\pi i k x_j}\rVert$.

Equivalently: for every $M$, there exists $k > 0$ such that
$\lVert\sum_{j < n} e^{2\pi i k x_j}\rVert \geq M$ for infinitely many $n$.
(This is equivalent to $\limsup_{k \to \infty} A_k = \infty$ since
$\sup_k = \infty \iff \limsup_k = \infty$ for extended-real-valued sequences.)
-/
@[category research open, AMS 11 42]
theorem erdos_987 :
    ∀ (x : ℕ → ℝ), (∀ j, x j ∈ Set.Ioo 0 1) →
    ∀ M : ℝ, ∃ k : ℕ, 0 < k ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      M ≤ ‖exponentialSum x k n‖ := by
  sorry

/--
Erdős Problem 987, Part 2 [Er65b][Ha74]:
It is not possible for $A_k = o(k)$. For any sequence $x_1, x_2, \ldots \in (0,1)$,
there exists $c > 0$ such that for infinitely many $k$,
$\lVert\sum_{j < n} e^{2\pi i k x_j}\rVert \geq c \cdot k$ for infinitely many $n$.
-/
@[category research open, AMS 11 42]
theorem erdos_987.variants.not_little_o :
    ∀ (x : ℕ → ℝ), (∀ j, x j ∈ Set.Ioo 0 1) →
    ∃ c : ℝ, 0 < c ∧ ∀ K₀ : ℕ, ∃ k : ℕ, K₀ ≤ k ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c * ↑k ≤ ‖exponentialSum x k n‖ := by
  sorry

end Erdos987
