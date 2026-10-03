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
# Erdős Problem 611

*References:*
- [erdosproblems.com/611](https://www.erdosproblems.com/611)
- [EGT92] Erdős, Paul and Gallai, Tibor and Tuza, Zsolt, *Covering the cliques of a graph with
  vertices*. Discrete Math. (1992), 279-289.
- [Er94] Erdős, P., *Problems and results on set systems and hypergraphs*. Extremal problems for
  finite sets (Visegrád, 1991) (1994), 217-227.
- [Er99] Erdős, Paul, *A selection of problems and results in combinatorics*. Combin. Probab.
  Comput. (1999), 1-6.
-/

@[expose] public section

open Filter

namespace Erdos611

/--
`IsCliqueTransversal G S` means that the vertex set `S` meets every maximal clique of `G`.

A maximal clique is a `Finset` of vertices that is a clique and is maximal under inclusion among
cliques.
-/
def IsCliqueTransversal {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ C : Finset V, Maximal (fun T : Finset V ↦ G.IsClique (T : Set V)) C → ∃ v ∈ C, v ∈ S

/--
`cliqueTransversalNum G` is the clique transversal number $\tau(G)$: the least number of vertices
that include at least one vertex from each maximal clique of `G`.
-/
noncomputable def cliqueTransversalNum {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ S : Finset V, S.card = k ∧ IsCliqueTransversal G S}

/-- `AllMaximalCliquesAtLeast G k` means that every maximal clique of `G` has at least `k`
vertices. -/
def AllMaximalCliquesAtLeast {V : Type} (G : SimpleGraph V) (k : ℝ) : Prop :=
  ∀ s ∈ G.cliqueSizes, k ≤ (s : ℝ)

/--
`cliqueThreshold c n` is $k_c(n)$: the least $k$ such that every graph on $n$ vertices whose
maximal cliques all have at least $k$ vertices satisfies $\tau(G) < (1 - c)n$.
-/
noncomputable def cliqueThreshold (c : ℝ) (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ G : SimpleGraph (Fin n), AllMaximalCliquesAtLeast G (k : ℝ) →
    (cliqueTransversalNum G : ℝ) < (1 - c) * (n : ℝ)}

/--
For a graph $G$ let $\tau(G)$ denote the minimal number of vertices that include at least one
from each maximal clique of $G$. Is it true that if all maximal cliques in $G$ have at least $cn$
vertices then $\tau(G) = o_c(n)$?

Here $n$ is the number of vertices, and $o_c(n)$ is uniform over all such graphs on $n$ vertices.
-/
@[category research open, AMS 5]
theorem erdos_611.parts.i : answer(sorry) ↔
    ∀ c > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      AllMaximalCliquesAtLeast G (c * (n : ℝ)) →
        (cliqueTransversalNum G : ℝ) ≤ ε * (n : ℝ) := by
  sorry

/--
For $0 < c < 1$, estimate the minimal $k_c(n)$ such that if every maximal clique in a graph $G$
on $n$ vertices has at least $k_c(n)$ vertices then $\tau(G) < (1 - c)n$.

We require $c < 1$: for $c \geq 1$ the bound $\tau(G) < (1 - c)n \leq 0$ is impossible, so
$k_c(n)$ is degenerate. Erdős, Gallai, and Tuza [EGT92] proved a lower bound of the form
$k_c(n) \geq n^{c'/\log\log n}$ for some $c' > 0$ (as reported on erdosproblems.com).
-/
@[category research open, AMS 5]
theorem erdos_611.parts.ii :
    ∀ c : ℝ, 0 < c → c < 1 →
      (fun n ↦ (cliqueThreshold c n : ℝ)) =Θ[atTop] (answer(sorry) : ℝ → ℕ → ℝ) c := by
  sorry

/--
Bollobás and Erdős proved that if every maximal clique of a graph $G$ on $n$ vertices has at
least $n + 3 - 2\sqrt{n}$ vertices then $\tau(G) = 1$ (as reported on erdosproblems.com).
-/
@[category research solved, AMS 5]
theorem erdos_611.variants.bollobas_erdos :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      AllMaximalCliquesAtLeast G ((n : ℝ) + 3 - 2 * Real.sqrt (n : ℝ)) →
        cliqueTransversalNum G = 1 := by
  sorry

/--
The threshold $n + 3 - 2\sqrt{n}$ of Bollobás and Erdős is best possible. We formalise this as:
for every $n = m^2$ with $m \geq 2$ there is a graph on $n$ vertices whose maximal cliques all
have at least $n + 2 - 2\sqrt{n} = m^2 + 2 - 2m$ vertices and with $\tau(G) \geq 2$.
-/
@[category research solved, AMS 5]
theorem erdos_611.variants.bollobas_erdos_sharp :
    ∀ m : ℕ, 2 ≤ m → ∃ G : SimpleGraph (Fin (m ^ 2)),
      AllMaximalCliquesAtLeast G ((m : ℝ) ^ 2 + 2 - 2 * (m : ℝ)) ∧
        2 ≤ cliqueTransversalNum G := by
  sorry

end Erdos611
