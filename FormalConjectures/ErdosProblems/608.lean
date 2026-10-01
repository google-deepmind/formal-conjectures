/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 608

*References:*
- [erdosproblems.com/608](https://www.erdosproblems.com/608)
- [EFR92] Erdős, P. and Faudree, R. J. and Rousseau, C. C., *Extremal problems involving vertices
  and edges on odd cycles*. Discrete Math. (1992), 23--31.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math. (1997),
  81--85.
- [GHV19] Grzesik, Andrzej and Hu, Ping and Volec, Jan, *Minimum number of edges that occur in
  odd cycles*. J. Combin. Theory Ser. B (2019), 65--103.
-/

@[expose] public section

open Filter SimpleGraph

namespace Erdos608

/-- The edges of `G` which are contained in a cycle of length `k`. -/
def edgesInCycle {V : Type*} (G : SimpleGraph V) (k : ℕ) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = k ∧ e ∈ c.edges}

/--
Let $G$ be a graph with $n$ vertices and $>n^2/4$ many edges. Are there at least $\frac{2}{9}n^2$
edges of $G$ which are contained in a $C_5$?

Erdős, Faudree, and Rousseau [EFR92] proved that any graph on $n$ vertices with $>n^2/4$ edges
contains at least $2\lfloor n/2\rfloor+1$ edges in triangles. Erdős [Er97d] stated that, under
the same assumptions, there at least $\frac{2}{9}n^2$ edges of $G$ which are contained in some
odd cycle - this is best possible, as witnessed by taking a complete graph on
$\lfloor \frac{2n+4}{3}\rfloor$ and a complete balanced bipartite graph on
$\lfloor \frac{n+1}{3}\rfloor$ vertices, which overlap on exactly one vertex.

Erdős, Faudree, and Rousseau [EFR92] ask, more generally, if for any fixed $k\geq 2$ every graph
with $n$ vertices and $>n^2/4$ edges contains at least $\frac{2}{9}n^2-O_k(n)$ edges which are
contained in a $C_{2k+1}$. The answer to the original question with $C_5$ is no - Füredi and
Maleki (in unpublished work which is described by Grzesik, Hu, and Volec [GHV19]) have
constructed graphs with $n$ vertices and $>n^2/4$ edges in which the number of edges contained
in a $C_5$ is at most $cn^2+O(n)$ where
$$c=\frac{2+\sqrt{2}}{16}\approx 0.2134.$$
This is the best possible: Grzesik, Hu, and Volec [GHV19] have proved that a graph on $n$
vertices with $>n^2/4$ edges contains at least $(c-o(1))n^2$ edges in a $C_5$. They further prove
the conjecture of Erdős, Faudree, and Rousseau [EFR92] for all $k\geq 3$ (that $>n^2/4$ edges
ensures at least $\frac{2}{9}n^2-O(n)$ edges in a $C_{2k+1}$).

The question is asked for all sufficiently large $n$ (for $n = 3$ it fails trivially, since
$K_3$ has $> 9/4$ edges and no $C_5$).
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos608.lean#L33"]
theorem erdos_608 : answer(False) ↔ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
    n ^ 2 < 4 * G.edgeSet.ncard → 2 * n ^ 2 ≤ 9 * (edgesInCycle G 5).ncard := by
  sorry

/--
Grzesik, Hu, and Volec [GHV19] have proved that a graph on $n$ vertices with $>n^2/4$ edges
contains at least $(c-o(1))n^2$ edges in a $C_5$, where $c=\frac{2+\sqrt{2}}{16}$, and this is
best possible by the construction of Füredi and Maleki.
-/
@[category research solved, AMS 5]
theorem erdos_608.variants.five_cycle : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (∀ G : SimpleGraph (Fin n), n ^ 2 < 4 * G.edgeSet.ncard →
      ((2 + √2) / 16 - ε) * n ^ 2 ≤ (edgesInCycle G 5).ncard) ∧
    ∃ G : SimpleGraph (Fin n), n ^ 2 < 4 * G.edgeSet.ncard ∧
      ((edgesInCycle G 5).ncard : ℝ) ≤ ((2 + √2) / 16 + ε) * n ^ 2 := by
  sorry

/--
Grzesik, Hu, and Volec [GHV19] proved the conjecture of Erdős, Faudree, and Rousseau [EFR92] for
all $k\geq 3$: a graph on $n$ vertices with $>n^2/4$ edges contains at least
$\frac{2}{9}n^2-O_k(n)$ edges which are contained in a $C_{2k+1}$.
-/
@[category research solved, AMS 5]
theorem erdos_608.variants.odd_cycle (k : ℕ) (hk : 3 ≤ k) : ∃ C : ℝ, ∀ n : ℕ,
    ∀ G : SimpleGraph (Fin n), n ^ 2 < 4 * G.edgeSet.ncard →
      (2 / 9 : ℝ) * n ^ 2 - C * n ≤ (edgesInCycle G (2 * k + 1)).ncard := by
  sorry

/--
Erdős, Faudree, and Rousseau [EFR92] proved that any graph on $n$ vertices with $>n^2/4$ edges
contains at least $2\lfloor n/2\rfloor+1$ edges in triangles.
-/
@[category research solved, AMS 5]
theorem erdos_608.variants.triangles (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : n ^ 2 < 4 * G.edgeSet.ncard) : 2 * (n / 2) + 1 ≤ (edgesInCycle G 3).ncard := by
  sorry

end Erdos608
