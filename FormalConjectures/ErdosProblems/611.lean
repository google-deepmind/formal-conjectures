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
# Erdős Problem 611

*Reference:* [erdosproblems.com/611](https://www.erdosproblems.com/611)

Let $\tau(G)$ denote the minimum number of vertices needed to intersect every maximal
clique of a graph $G$. Erdős, Gallai, and Tuza conjectured that if every maximal clique
of $G$ on $n$ vertices has at least $cn$ vertices (for a fixed constant $c > 0$), then
$\tau(G) = o(n)$.

[EGT92] Erdős, P., Gallai, T., and Tuza, Zs., _Covering the cliques of a graph with vertices_.
Discrete Mathematics (1992), 279-289.

[Er94] Erdős, P., _Some old and new problems in various branches of combinatorics_.
Discrete Mathematics (1994).

[Er99] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Matematiche (Catania) (1999).
-/

open SimpleGraph

namespace Erdos611

/-- $S$ is a maximal clique of $G$ (as a `Finset`): it is a clique and no vertex
    outside $S$ can be added while preserving the clique property. -/
def IsMaximalCliqueFS {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  G.IsClique (S : Set (Fin n)) ∧
  ∀ v : Fin n, v ∉ S → ¬G.IsClique (↑(insert v S) : Set (Fin n))

/-- $T$ is a clique transversal of $G$ if $T$ meets every maximal clique of $G$
    that has at least $2$ vertices. -/
def IsCliqueTransversal {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), IsMaximalCliqueFS G S → 2 ≤ S.card → (T ∩ S).Nonempty

/-- The clique transversal number $\tau(G)$: the minimum cardinality of a clique
    transversal of $G$. -/
noncomputable def cliqueTransversalNum {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf { k : ℕ | ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧ T.card = k }

/-- Every maximal clique of $G$ with at least $2$ vertices has at least $m$ vertices. -/
def AllMaxCliquesAtLeast {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∀ S : Finset (Fin n), IsMaximalCliqueFS G S → 2 ≤ S.card → m ≤ S.card

/--
**Erdős Problem 611** (Main conjecture) [EGT92][Er94][Er99]:

If all maximal cliques in $G$ have at least $cn$ vertices then $\tau(G) = o_c(n)$.

Formulated as: for every $c > 0$ and $\varepsilon > 0$, there exists $N_0$ such that for all
$n \ge N_0$, every graph $G$ on $n$ vertices in which every maximal clique has at
least $\lceil c \cdot n \rceil$ vertices satisfies $\tau(G) \le \varepsilon \cdot n$.
-/
@[category research open, AMS 5]
theorem erdos_611 (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ G : SimpleGraph (Fin n),
        AllMaxCliquesAtLeast G (⌈c * (n : ℝ)⌉₊) →
        (cliqueTransversalNum G : ℝ) ≤ ε * (n : ℝ) := by
  sorry

/--
**Erdős Problem 611** (Known bound, Erdős-Gallai-Tuza) [EGT92]:

If every maximal clique of $G$ on $n$ vertices has at least $k$ vertices then
$\tau(G) \le n - \sqrt{kn}$.
-/
@[category research solved, AMS 5]
theorem erdos_611.variants.known_bound (n : ℕ) (hn : n ≥ 1)
    (G : SimpleGraph (Fin n)) (k : ℕ) (hk : k ≥ 1)
    (hclique : AllMaxCliquesAtLeast G k) :
    (cliqueTransversalNum G : ℝ) ≤ (n : ℝ) - Real.sqrt ((k : ℝ) * (n : ℝ)) := by
  sorry

/--
**Erdős Problem 611** (Bollobás-Erdős):

If every maximal clique of $G$ on $n$ vertices has at least $n + 3 - 2\sqrt{n}$ vertices
then $\tau(G) \le 1$. (This threshold is best possible.)
-/
@[category research solved, AMS 5]
theorem erdos_611.variants.bollobas_erdos (n : ℕ) (hn : n ≥ 4)
    (G : SimpleGraph (Fin n)) :
    AllMaxCliquesAtLeast G (⌈(n : ℝ) + 3 - 2 * Real.sqrt (n : ℝ)⌉₊) →
    cliqueTransversalNum G ≤ 1 := by
  sorry

/--
**Erdős Problem 611** (k_c(n) estimation) [EGT92]:

For $c > 0$, let $k_c(n)$ be the minimal value such that if every maximal clique of $G$ on
$n$ vertices has at least $k_c(n)$ vertices, then $\tau(G) < (1 - c) n$. Erdős, Gallai, and
Tuza proved that $k_c(n) \ge n^{c' / \log \log n}$ for some $c' > 0$ depending on $c$.
-/
@[category research solved, AMS 5]
theorem erdos_611.variants.kc_lower_bound (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∃ c' : ℝ, c' > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ G : SimpleGraph (Fin n),
        AllMaxCliquesAtLeast G ⌈(n : ℝ) ^ (c' / Real.log (Real.log (n : ℝ)))⌉₊ →
        (cliqueTransversalNum G : ℝ) < (1 - c) * (n : ℝ) := by
  sorry

end Erdos611
