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
# Erdős Problem 311

*Reference:* [erdosproblems.com/311](https://www.erdosproblems.com/311)

Let δ(N) denote the minimal non-zero value of |1 − Σ_{n ∈ A} 1/n| over subsets A of {1, …, N}.
The problem conjectures that δ(N) = e^{-(c+o(1))·N} for some constant c ∈ (0, 1).

The original formulation in [ErGr80] additionally required that A contain no subset S with
∑_{n ∈ S} 1/n = 1 (i.e., A is Egyptian-1-free). Kovac showed that this restriction does not
affect the value of δ(N), so the two formulations are equivalent.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980), p. 40.
-/

open Real

namespace Erdos311

/-- The minimal non-zero value of $\left|1 - \sum_{n \in A} \frac{1}{n}\right|$ as $A$ ranges over
all subsets of $\{1, \ldots, N\}$. -/
noncomputable def unitFractionDeviation (N : ℕ) : ℝ :=
  sInf { x : ℝ | x > 0 ∧ ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    x = |1 - ∑ n ∈ A, (1 : ℝ) / n| }

/--
Erdős Problem 311 [ErGr80, p. 40]:

Let $\delta(N)$ be the minimal non-zero value of $\left|1 - \sum_{n \in A} \frac{1}{n}\right|$ as
$A$ ranges over all subsets of $\{1, \ldots, N\}$. The conjecture asserts that
$\delta(N) = e^{-(c+o(1))N}$ for some constant $c \in (0, 1)$.

Equivalently, there exists $c \in (0, 1)$ such that for all $\varepsilon > 0$ and all
sufficiently large $N$:
$$e^{-(c + \varepsilon) \cdot N} \le \delta(N) \le e^{-(c - \varepsilon) \cdot N}.$$
-/
@[category research open, AMS 11]
theorem erdos_311 : answer(sorry) ↔
    (∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      exp (-(c + ε) * N) ≤ unitFractionDeviation N ∧
      unitFractionDeviation N ≤ exp (-(c - ε) * N)) := by
  sorry

end Erdos311
