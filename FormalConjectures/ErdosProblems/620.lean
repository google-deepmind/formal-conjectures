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
# Erdős Problem 620

*Reference:* [erdosproblems.com/620](https://www.erdosproblems.com/620)

The Erdős-Rogers problem: If $G$ is a graph on $n$ vertices without a $K_4$, how large a
triangle-free induced subgraph must $G$ contain?

Let $f(n)$ be the largest $m$ such that every $K_4$-free graph on $n$ vertices contains a
triangle-free induced subgraph with at least $m$ vertices. It is known that
$f(n) = n^{1/2+o(1)}$.

The best bounds currently known are:
$$n^{1/2} \cdot (\log n)^{1/2} / \log(\log n) \ll f(n) \ll n^{1/2} \cdot \log n$$

The lower bound follows from results of Shearer [Sh95], and the upper bound was proved by
Mubayi and Verstraëte [MuVe24].

The precise asymptotic behaviour of $f(n)$ remains open. The formalized statements below
capture the known result $f(n) = n^{1/2+o(1)}$; the original Erdős-Rogers problem of
determining the precise asymptotics remains open.

[ErRo62] Erdős, P. and Rogers, C.A., _The construction of certain graphs_.
Canadian Journal of Mathematics **14** (1962), 702-707.

[BoHi91] Bollobás, B. and Hind, H.R., _Graphs without large triangle free subgraphs_.
Discrete Mathematics (1991), 119-131.

[Kr94] Krivelevich, M., _$K^s$-free graphs without large $K^r$-free subgraphs_.
Combinatorics, Probability and Computing (1994), 349-354.

[Sh95] Shearer, J.B., _On the independence number of sparse graphs_.
Random Structures and Algorithms (1995), 269-271.

[Er99] Erdős, P.

[Wo13] Wolfovitz, G., _$K_4$-free graphs without large induced triangle-free subgraphs_.
Combinatorica (2013), 623-631.

[MuVe24] Mubayi, D. and Verstraëte, J., _On the order of Erdős-Rogers functions_.
arXiv:2401.02548 (2024).
-/

open SimpleGraph Finset

namespace Erdos620

/--
Erdős Problem 620 (lower bound direction of the Erdős-Rogers problem):
For all $\varepsilon > 0$, for sufficiently large $n$, every $K_4$-free graph on $n$ vertices
contains a triangle-free induced subgraph of size at least $n^{1/2 - \varepsilon}$.

Together with `erdos_620.variants.upper`, this captures the known result
$f(n) = n^{1/2+o(1)}$. The original Erdős-Rogers problem of determining the precise
asymptotics of $f(n)$ remains open.

[ErRo62], [Sh95]
-/
@[category research solved, AMS 5]
theorem erdos_620 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∀ (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
    ∃ (S : Finset (Fin n)),
      (G.induce (↑S : Set (Fin n))).CliqueFree 3 ∧
      (S.card : ℝ) ≥ (n : ℝ) ^ ((1 : ℝ) / 2 - ε) := by
  sorry

/--
Erdős Problem 620 (upper bound direction of the Erdős-Rogers problem):
For all $\varepsilon > 0$, for sufficiently large $n$, there exists a $K_4$-free graph on $n$
vertices such that every triangle-free induced subgraph has at most $n^{1/2 + \varepsilon}$
vertices.

[MuVe24]
-/
@[category research solved, AMS 5]
theorem erdos_620.variants.upper :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ (G : SimpleGraph (Fin n)),
      G.CliqueFree 4 ∧
      ∀ (S : Finset (Fin n)),
        (G.induce (↑S : Set (Fin n))).CliqueFree 3 →
        (S.card : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  sorry

end Erdos620
