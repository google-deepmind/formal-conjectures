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
# Erdős Problem 616

*Reference:* [erdosproblems.com/616](https://www.erdosproblems.com/616)

Let $r \geq 3$. For an $r$-uniform hypergraph $G$ let $\tau(G)$ denote the covering number
(or transversal number), the minimum size of a set of vertices which includes
at least one from each edge in $G$.

Determine the best possible $t$ such that, if $G$ is an $r$-uniform hypergraph
where every subgraph $G'$ on at most $3r - 3$ vertices has $\tau(G') \leq 1$, we have
$\tau(G) \leq t$.

[EHT91] Erdős, P., Hajnal, A., and Tuza, Zs., _Local constraints ensuring small representing
sets_. J. Combin. Theory Ser. A 58 (1991), 78-84.
-/

open Finset

namespace Erdos616

/-- An $r$-uniform hypergraph on vertex set `Fin n`. -/
structure UniformHypergraph (n r : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = r

/-- A set $S$ of vertices is a transversal of hypergraph $G$ if it meets every edge. -/
def IsTransversal {n r : ℕ} (G : UniformHypergraph n r) (S : Finset (Fin n)) : Prop :=
  ∀ e ∈ G.edges, ∃ v ∈ S, v ∈ e

/-- The covering number $\tau(G)$: the minimum size of a transversal. -/
noncomputable def coveringNumber {n r : ℕ} (G : UniformHypergraph n r) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (Fin n), S.card = k ∧ IsTransversal G S}

/-- The subhypergraph of $G$ induced on vertex set $W$: edges of $G$ contained in $W$. -/
def inducedSub {n r : ℕ} (G : UniformHypergraph n r) (W : Finset (Fin n)) :
    UniformHypergraph n r where
  edges := G.edges.filter (· ⊆ W)
  uniform := fun e he => G.uniform e (Finset.mem_filter.mp he).1

/-- The local covering property: every induced subhypergraph on at most
$3r - 3$ vertices has covering number at most $1$. -/
def HasLocalCoveringProperty {n r : ℕ} (G : UniformHypergraph n r) : Prop :=
  ∀ W : Finset (Fin n), W.card ≤ 3 * r - 3 → coveringNumber (inducedSub G W) ≤ 1

/--
Erdős Problem 616 — Upper bound [EHT91]:
If $G$ is an $r$-uniform hypergraph ($r \geq 3$) where every subhypergraph on at most
$3r - 3$ vertices has covering number $\leq 1$, then $\tau(G) \leq \frac{1}{5}r$.
-/
@[category research solved, AMS 5]
theorem erdos_616 :
    ∀ r : ℕ, 3 ≤ r →
    ∀ n : ℕ, ∀ G : UniformHypergraph n r,
    HasLocalCoveringProperty G →
    (coveringNumber G : ℝ) ≤ (1 : ℝ) / 5 * (r : ℝ) := by
  sorry

/--
Erdős Problem 616 — Lower bound [EHT91]:
For every $r \geq 3$, there exists an $r$-uniform hypergraph $G$ satisfying the local
covering property with $\tau(G) \geq \frac{3}{16}r + \frac{7}{8}$.
-/
@[category research solved, AMS 5]
theorem erdos_616.variants.lower_bound :
    ∀ r : ℕ, 3 ≤ r →
    ∃ n : ℕ, ∃ G : UniformHypergraph n r,
    HasLocalCoveringProperty G ∧
    (coveringNumber G : ℝ) ≥ (3 : ℝ) / 16 * (r : ℝ) + 7 / 8 := by
  sorry

end Erdos616
