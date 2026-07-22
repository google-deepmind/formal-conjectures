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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 209

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

Per the WOWII definitions, $\lambda(v)$ is the local independence number (the
independence number of the subgraph induced on the neighbourhood of $v$, i.e.
`indepNeighborsCard`), $\lambda_{\max}(G)$ is its maximum over all vertices,
and the *frequency* of $\lambda_{\max}(G)$ is the number of vertices attaining
the maximum. Note that the original statement reads $|E(\bar G)|$ — the edge
count of the **complement** (rendered with an overline that is easy to miss in
plain-text copies of the list).

## Counterexample

For every $m \geq 7$, take a clique $K_m$ with a distinguished vertex $s$; add
two nonadjacent vertices, each adjacent to all of the clique except $s$; and
add two pendant vertices adjacent exactly to $s$. The resulting connected
graph on $m + 4$ vertices has $\lambda_{\max} = 3$ attained exactly at the $m$
clique vertices, and $|E(\bar G)| = 2m + 6$, so the premise
$(1/6)(1 + 2|E(\bar G)|) \leq \operatorname{freq}(\lambda_{\max})$ becomes
$4m + 13 \leq 6m$, which holds for all $m \geq 7$. Both pendant vertices must
be endpoints of any Hamiltonian path, yet both attach to the same vertex $s$,
so no Hamiltonian path exists.

The smallest member ($m = 7$) has 11 vertices and graph6 encoding
`J?o}]^Nr}^_`; an exhaustive search over all 1,018,690,325 connected graphs
on $4 \leq n \leq 11$ vertices (graphs on at most 3 vertices are trivially
traceable) shows it is the unique counterexample of minimum order.
-/

namespace WrittenOnTheWallII.GraphConjecture209

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The maximum local independence number $\lambda_{\max}(G)$: the maximum
over all vertices $v$ of the independence number of the subgraph induced on
the neighbourhood of $v$. -/
noncomputable def lambdaMax (G : SimpleGraph α) : ℕ :=
  Finset.univ.sup fun v => indepNeighborsCard G v

/-- The frequency of $\lambda_{\max}(G)$: the number of vertices whose local
independence number attains the maximum. -/
noncomputable def lambdaMaxFreq (G : SimpleGraph α) : ℕ :=
  (Finset.univ.filter fun v => indepNeighborsCard G v = lambdaMax G).card

/--
WOWII [Conjecture 209](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

If $G$ is a simple connected graph with $n > 1$ such that
$\frac{1}{6}\left(1 + 2\,|E(\bar G)|\right) \leq$ frequency of
$\lambda_{\max}(G)$, then $G$ has a Hamiltonian path. Here $\bar G$ is the
complement of $G$, $\lambda_{\max}(G)$ is the maximum over all vertices of the
independence number of the neighbourhood, and the frequency is the number of
vertices attaining that maximum.

This conjecture is false. The counterexample family in the module docstring
satisfies the premise and has no Hamiltonian path.
-/
@[category research solved, AMS 5, formal_proof using formal_conjectures at
  "https://github.com/infinityscroll/formal-conjectures/blob/5780128350a91f732ca1cacc439d59d25976206e/FormalConjectures/WrittenOnTheWallII/GraphConjecture209Counterexample.lean"]
theorem conjecture209 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected),
      (1 : ℝ) / 6 * (1 + 2 * ((Gᶜ).edgeFinset.card : ℝ)) ≤ lambdaMaxFreq G →
      ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry

-- Sanity checks

/-- On the complete graph `K₃` every neighbourhood induces `K₂`, so the
maximum local independence number is `1`. -/
@[category test, AMS 5]
example : lambdaMax (⊤ : SimpleGraph (Fin 3)) = 1 := by
  unfold lambdaMax
  simp_rw [indepNeighborsCard, indep_num_eq_computable]
  decide +native

/-- On `K₃` all three vertices attain the maximum local independence number. -/
@[category test, AMS 5]
example : lambdaMaxFreq (⊤ : SimpleGraph (Fin 3)) = 3 := by
  unfold lambdaMaxFreq lambdaMax
  simp_rw [indepNeighborsCard, indep_num_eq_computable]
  decide +native

/-- On the edgeless graph all local independence numbers are `0`, so all
vertices attain the maximum. -/
@[category test, AMS 5]
example : lambdaMaxFreq (⊥ : SimpleGraph (Fin 3)) = 3 := by
  unfold lambdaMaxFreq lambdaMax
  simp_rw [indepNeighborsCard, indep_num_eq_computable]
  decide +native

end WrittenOnTheWallII.GraphConjecture209
