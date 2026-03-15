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
# Erdős Problem 78

*Reference:* [erdosproblems.com/78](https://www.erdosproblems.com/78)

Give a constructive proof that $R(k) > C^k$ for some constant $C > 1$, where $R(k)$ is the
diagonal Ramsey number. Erdős's probabilistic proof that $R(k) \gg k \cdot 2^{k/2}$ is
non-constructive. Prize: \$100.

Partial progress: Cohen [Co15] constructed a graph on $n$ vertices with no clique or independent
set of size $\geq 2^{(\log \log n)^C}$. Li [Li23b] improved this to $(\log n)^C$.

See also OEIS sequence A059442 and related problems #77, #1029.

[Er69b] Erdős, P., _Some applications of Ramsey's theorem to additive number theory_.
European J. Combin. (1969).

[Er71] Erdős, P., _On some extremal problems on r-graphs_. Discrete Math. **1** (1971), 1–6.

[Er88] Erdős, P., _Problems and results on chromatic numbers in finite and infinite graphs_.
Graph Theory with Applications to Algorithms and Computer Science (1988).

[Er93] Erdős, P., _On some of my favourite theorems_. Combinatorics, Paul Erdős is Eighty,
Vol. 2 (1993), p. 337.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Congressus Numerantium **107** (1995).

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.

[Va99] Vaughan, R. C., _On the number of monochromatic complete subgraphs_. (1999), 3.49.

[Co15] Cohen, D., _Two-source dispersers for polylogarithmic entropy and improved Ramsey
graphs_. (2015).

[Li23b] Li, Z., _Explicit Ramsey graphs and two-source extractors_. (2023).
-/

open SimpleGraph

namespace Erdos78

/--
Erdős Problem 78 (Open, \$100 prize):

Let $R(k)$ be the Ramsey number for $K_k$, the minimal $n$ such that every
2-colouring of the edges of $K_n$ contains a monochromatic copy of $K_k$.
Give a constructive proof that $R(k) > C^k$ for some constant $C > 1$.

Erdős gave a simple probabilistic (non-constructive) proof that
$R(k) \gg k \cdot 2^{k/2}$. This problem asks for an explicit/constructive
lower bound that is still exponential in $k$.

Equivalently, this asks for an explicit construction of a graph on $n$
vertices which does not contain any clique or independent set of size
$\geq c \cdot \log(n)$ for some constant $c > 0$.

We formalize the core mathematical content: there exists $C > 1$ such that
for all $k \geq 2$, there exists a graph on at least $C^k$ vertices with no
clique or independent set of size $k$ (an independent set of size $k$ in $G$
is equivalent to a clique of size $k$ in the complement $G^c$, by
`SimpleGraph.isClique_compl`). The "constructive" requirement pertains
to the nature of the proof, not the formal statement itself.
-/
@[category research open, AMS 5]
theorem erdos_78 :
    ∃ C : ℝ, C > 1 ∧ ∀ k : ℕ, k ≥ 2 →
      ∃ n : ℕ, (C ^ k : ℝ) ≤ ↑n ∧
        ∃ G : SimpleGraph (Fin n),
          G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  sorry

/--
Erdős Problem 78 — $o(\sqrt{n})$ variant [Er69b]:

Erdős also asked for an explicit construction of a graph on $n$ vertices
with no clique or independent set of size $o(\sqrt{n})$. This is weaker
than the full exponential lower bound. The website notes this is now known.
-/
@[category research solved, AMS 5]
theorem erdos_78_variant_sqrt :
    ∃ (f : ℕ → ℕ), (∀ n, f n < n) ∧
      Filter.Tendsto (fun n => (f n : ℝ) / n ^ (1/2 : ℝ)) Filter.atTop (nhds 0) ∧
      ∀ n, ∃ G : SimpleGraph (Fin n), G.CliqueFree (f n) ∧ Gᶜ.CliqueFree (f n) := by
  sorry

/--
Erdős Problem 78 — logarithmic formulation:

Equivalently, there exists a constant $c > 0$ such that for all $n \geq 2$,
there is a graph on $n$ vertices with no clique or independent set of size
$\geq c \cdot \log(n)$. This is logically equivalent to `erdos_78` but
phrased in the "construct a graph on $n$ vertices" framing.
-/
@[category research open, AMS 5]
theorem erdos_78_log :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      ∃ G : SimpleGraph (Fin n),
        G.CliqueFree ⌈c * Real.log n⌉₊ ∧ Gᶜ.CliqueFree ⌈c * Real.log n⌉₊ := by
  sorry

end Erdos78
