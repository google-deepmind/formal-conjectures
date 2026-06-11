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
# Erdős–Hajnal conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Hajnal_conjecture)

*References:*
* [ErHa89] Erdős, P. and Hajnal, A. (1989). "Ramsey-type theorems."
  *Discrete Appl. Math.* 25, pp. 37--52.
* [CSSS23] Chudnovsky, M., Scott, A., Seymour, P. and Spirkl, S. (2023).
  "Erdős–Hajnal for graphs with no 5-hole." *Proc. Lond. Math. Soc. (3)* 126, pp. 997--1014.
* [NSS23] Nguyen, T., Scott, A. and Seymour, P. (2023).
  "Induced subgraph density. VII. The five-vertex path."
  [arXiv:2312.15333](https://arxiv.org/abs/2312.15333)
-/

open SimpleGraph

namespace ErdosHajnalConjecture

/--
**Erdős–Hajnal conjecture.** For every graph $H$ there exists a constant
$\varepsilon = \varepsilon(H) > 0$ such that every $H$-free graph $G$ on $n$ vertices (that is,
$G$ contains no induced subgraph isomorphic to $H$) has a clique or an independent set of size
at least $n^{\varepsilon}$. [ErHa89]

Here `H ⊴ G` is `SimpleGraph.IsIndContained`, i.e. `G` contains an induced copy of `H`.
-/
@[category research open, AMS 5]
theorem erdos_hajnal_conjecture (k : ℕ) (H : SimpleGraph (Fin k)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ¬ H ⊴ G → (n : ℝ) ^ ε ≤ (max G.cliqueNum G.indepNum : ℝ) := by
  sorry

/--
Erdős and Hajnal proved the following weaker bound: for every graph $H$ there exists
$c = c(H) > 0$ such that every $H$-free graph $G$ on $n \geq 2$ vertices has a clique or an
independent set of size at least $e^{c\sqrt{\log n}}$. [ErHa89]
-/
@[category research solved, AMS 5]
theorem erdos_hajnal_conjecture.variants.erdos_hajnal_lower (k : ℕ) (H : SimpleGraph (Fin k)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 2 ≤ n →
      ¬ H ⊴ G →
      Real.exp (c * Real.sqrt (Real.log n)) ≤ (max G.cliqueNum G.indepNum : ℝ) := by
  sorry

/--
The case $H = P_5$, the path on five vertices: every $P_5$-free graph on $n$ vertices has a
clique or an independent set of polynomial size. This was proved by Nguyen, Scott and
Seymour. [NSS23]
-/
@[category research solved, AMS 5]
theorem erdos_hajnal_conjecture.variants.p5_case :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ¬ pathGraph 5 ⊴ G → (n : ℝ) ^ ε ≤ (max G.cliqueNum G.indepNum : ℝ) := by
  sorry

/--
The case $H = C_5$, the cycle on five vertices: every graph on $n$ vertices with no induced
five-vertex cycle ("5-hole") has a clique or an independent set of polynomial size. This was
proved by Chudnovsky, Scott, Seymour and Spirkl. [CSSS23]
-/
@[category research solved, AMS 5]
theorem erdos_hajnal_conjecture.variants.c5_case :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ¬ cycleGraph 5 ⊴ G → (n : ℝ) ^ ε ≤ (max G.cliqueNum G.indepNum : ℝ) := by
  sorry

/--
Sanity check: on a single vertex the conjectured bound holds with $\varepsilon = 1$, since
every graph on one vertex has a clique of size $1 = 1^1$.
-/
@[category test, AMS 5]
theorem erdos_hajnal_conjecture.variants.one_vertex (G : SimpleGraph (Fin 1)) :
    ((1 : ℕ) : ℝ) ^ (1 : ℝ) ≤ (max G.cliqueNum G.indepNum : ℝ) := by
  have hc : G.IsClique ({0} : Finset (Fin 1)) := by simp
  have h1 : 1 ≤ G.cliqueNum := by
    simpa using IsClique.card_le_cliqueNum (tc := hc)
  have h : 1 ≤ max G.cliqueNum G.indepNum := h1.trans (le_max_left _ _)
  calc ((1 : ℕ) : ℝ) ^ (1 : ℝ) = 1 := by norm_num
    _ ≤ (max G.cliqueNum G.indepNum : ℝ) := by exact_mod_cast h

end ErdosHajnalConjecture
