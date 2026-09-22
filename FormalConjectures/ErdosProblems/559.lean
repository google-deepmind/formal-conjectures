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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 559

*References:*
- [erdosproblems.com/559](https://www.erdosproblems.com/559)
- [Be83b] Beck, József, _On size Ramsey number of paths, trees, and circuits. I_. J. Graph
  Theory (1983), 115-129.
- [FrPi87] Friedman, J. and Pippenger, N., _Expanding graphs contain all small trees_.
  Combinatorica (1987), 71-76.
- [HKL95] Haxell, P. E. and Kohayakawa, Y. and Łuczak, T., _The induced size-Ramsey number of
  cycles_. Combin. Probab. Comput. (1995), 217-239.
- [RoSz00] Rödl, Vojtěch and Szemerédi, Endre, _On size Ramsey numbers of graphs with bounded
  degree_. Combinatorica (2000), 257-262.
- [Ti22b] Tikhomirov, K., _On bounded degree graphs with large size-Ramsey numbers_.
  arXiv:2210.05818 (2022).
- [DrPe22] N. Draganić and K. Petrova, _Size-Ramsey numbers of graphs with maximum degree three_.
  arXiv:2207.05048 (2022).
-/

@[expose] public section

open Filter Real SimpleGraph

namespace Erdos559

open scoped Classical in
/--
Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such that there is
a graph $H$ with $m$ edges that is Ramsey for $G$.

If $G$ has $n$ vertices and maximum degree $d$ then prove that
$$\hat{R}(G)\ll_d n.$$

This was disproved for $d=3$ by Rödl and Szemerédi [RoSz00], who constructed a graph on $n$
vertices with maximum degree $3$ such that $\hat{R}(G)\gg n(\log n)^{c}$ for some absolute
constant $c>0$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos559.lean#L1275"]
theorem erdos_559 : answer(False) ↔
    ∀ d : ℕ, ∃ C : ℝ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      G.maxDegree ≤ d → (sizeRamsey G G : ℝ) ≤ C * Fintype.card V := by
  sorry

open scoped Classical in
/-- Rödl and Szemerédi [RoSz00] disproved the linear bound already for maximum degree $3$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos559.lean#L1275"]
theorem erdos_559.variants.degree_three :
    ¬ ∃ C : ℝ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      G.maxDegree ≤ 3 → (sizeRamsey G G : ℝ) ≤ C * Fintype.card V := by
  sorry

open scoped Classical in
/-- Rödl and Szemerédi [RoSz00] constructed, for infinitely many $n$, a graph on $n$ vertices
with maximum degree $3$ such that $\hat{R}(G)\gg n(\log n)^{c}$ for some absolute constant
$c>0$. -/
@[category research solved, AMS 5]
theorem erdos_559.variants.rodl_szemeredi :
    ∃ c > 0, ∃ C > 0, ∃ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      G.maxDegree ≤ 3 ∧ C * n * (log n) ^ c ≤ sizeRamsey G G := by
  sorry

open scoped Classical in
/-- Tikhomirov [Ti22b] improved this to $\hat{R}(G)\gg n\exp(c\sqrt{\log n})$. -/
@[category research solved, AMS 5]
theorem erdos_559.variants.tikhomirov :
    ∃ c > 0, ∃ C > 0, ∃ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      G.maxDegree ≤ 3 ∧ C * n * exp (c * √(log n)) ≤ sizeRamsey G G := by
  sorry

open scoped Classical in
/-- Friedman and Pippenger [FrPi87] proved the linear bound when $G$ is a tree. -/
@[category research solved, AMS 5]
theorem erdos_559.variants.trees (d : ℕ) :
    ∃ C : ℝ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      G.IsTree → G.maxDegree ≤ d → (sizeRamsey G G : ℝ) ≤ C * Fintype.card V := by
  sorry

open scoped Classical in
/-- The best known upper bound for graphs of maximum degree $3$ is $\hat{R}(G)\leq n^{3/2+o(1)}$,
due to Draganić and Petrova [DrPe22]. -/
@[category research solved, AMS 5]
theorem erdos_559.variants.draganic_petrova (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      G.maxDegree ≤ 3 → (sizeRamsey G G : ℝ) ≤ (n : ℝ) ^ (3 / 2 + ε : ℝ) := by
  sorry

end Erdos559
