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
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 813

*Reference:* [erdosproblems.com/813](https://www.erdosproblems.com/813)

A problem of Erdős and Hajnal [Er90b], who proved $n^{1/3} \ll h(n) \ll n^{1/2}$.
Bucić and Sudakov [BuSu23] proved $h(n) \gg n^{5/12 - o(1)}$.

[Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and
differences_. Mathematics of Ramsey theory, Algorithms Combin., 5 (1990), 12-28.

[BuSu23] Bucić, M. and Sudakov, B., _Large independent sets from local considerations_.
arXiv:2007.03667 (2023).
-/

open SimpleGraph Classical

namespace Erdos813

/-- A graph on $n$ vertices has the property that every subset of $7$ vertices
    contains a triangle (three mutually adjacent vertices). -/
def EverySevenSetHasTriangle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), S.card = 7 →
    ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c

/-- $h(n)$ is the minimum clique number over all graphs on $n$ vertices in which
    every set of $7$ vertices contains a triangle. -/
noncomputable def erdos813H (n : ℕ) : ℕ :=
  sInf (SimpleGraph.cliqueNum '' {G : SimpleGraph (Fin n) | EverySevenSetHasTriangle G})

/--
Erdős Problem 813 [Er90b]:

There exist constants $c_1, c_2 > 0$ such that for all sufficiently large $n$,
$$
  C_1 \cdot n^{1/3 + c_1} \leq h(n) \leq C_2 \cdot n^{1/2 - c_2}.
$$
-/
@[category research open, AMS 05]
theorem erdos_813 :
    ∃ c₁ : ℝ, c₁ > 0 ∧
    ∃ c₂ : ℝ, c₂ > 0 ∧
    ∃ C₁ : ℝ, C₁ > 0 ∧
    ∃ C₂ : ℝ, C₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C₁ * (n : ℝ) ^ ((1 : ℝ) / 3 + c₁) ≤ (erdos813H n : ℝ) ∧
      (erdos813H n : ℝ) ≤ C₂ * (n : ℝ) ^ ((1 : ℝ) / 2 - c₂) := by
  sorry

/--
Erdős–Hajnal basic bounds [Er90b]:

The known result $n^{1/3} \ll h(n) \ll n^{1/2}$, i.e., there exist constants
$C_1, C_2 > 0$ and a threshold $N_0$ such that for all $n \geq N_0$,
$C_1 \cdot n^{1/3} \leq h(n) \leq C_2 \cdot n^{1/2}$.
-/
@[category research solved, AMS 05]
theorem erdos_813_basic_bounds :
    ∃ C₁ : ℝ, C₁ > 0 ∧
    ∃ C₂ : ℝ, C₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C₁ * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (erdos813H n : ℝ) ∧
      (erdos813H n : ℝ) ≤ C₂ * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/--
Bucić–Sudakov lower bound [BuSu23]:

The improved lower bound $h(n) \gg n^{5/12 - o(1)}$, formalized as: for every $\varepsilon > 0$,
there exist $C > 0$ and $N_0$ such that $h(n) \geq C \cdot n^{5/12 - \varepsilon}$ for all
$n \geq N_0$. This partially resolves the lower bound side of the main conjecture since
$5/12 > 1/3$.
-/
@[category research solved, AMS 05]
theorem erdos_813_bucic_sudakov :
    ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C * (n : ℝ) ^ ((5 : ℝ) / 12 - ε) ≤ (erdos813H n : ℝ) := by
  sorry

end Erdos813
