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
# Erdős Problem 500

*Reference:* [erdosproblems.com/500](https://www.erdosproblems.com/500)

What is $\mathrm{ex}_3(n, K_4^3)$? That is, the largest number of $3$-edges which can be placed
on $n$ vertices so that there exists no $K_4^3$, a set of $4$ vertices which is covered
by all $4$ possible $3$-edges.

A problem of Turán. Turán observed that dividing the vertices into three equal
parts $X_1, X_2, X_3$, and taking the edges to be those triples that either have
exactly one vertex in each part or two vertices in $X_i$ and one vertex in $X_{i+1}$
(where $X_4 = X_1$) shows that
$$
  \mathrm{ex}_3(n, K_4^3) \geq (5/9 + o(1)) \binom{n}{3}.
$$
This is probably the truth. The current best upper bound is
$$
  \mathrm{ex}_3(n, K_4^3) \leq 0.5611666 \binom{n}{3},
$$
due to Razborov [Ra10].

See also: Problem 712 (general case for r-uniform, k-clique).

OEIS: [A140462](https://oeis.org/A140462)

[Er61] Erdős, P., _Problems in combinatorics_ (1961).

[Er71] Erdős, P., _Topics in combinatorial analysis_. Proc. Second Louisiana Conf. on
Combinatorics, Graph Theory and Computing (1971), 2–20.

[Er74c] Erdős, P., _Problems and results on combinatorial number theory III_ (1974).

[Er81] Erdős, P., _Combinatorial problems and results_ (1981).

[Ra10] Razborov, A., _On 3-hypergraphs with forbidden 4-vertex configurations_.
SIAM J. Discrete Math. (2010), 946–963.
-/

open Finset Filter

namespace Erdos500

/-- A $3$-uniform hypergraph on `Fin n` is $K_4^3$-free if every edge has exactly $3$
vertices and no $4$ vertices span all $4$ possible $3$-element subsets. -/
def IsK43Free {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ H, e.card = 3) ∧
  ∀ S : Finset (Fin n), S.card = 4 → ¬(S.powersetCard 3 ⊆ H)

/-- The $3$-uniform Turán number $\mathrm{ex}_3(n, K_4^3)$: the maximum number of $3$-element
subsets of an $n$-element set such that no $4$ vertices span all $4$ triples. -/
noncomputable def ex3K43 (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Finset (Finset (Fin n)), IsK43Free H ∧ H.card = m}

/--
Erdős Problem 500 — Turán's Hypergraph Conjecture [Er61][Er71][Er74c][Er81]:

The $3$-uniform Turán density for $K_4^3$ is exactly $5/9$. Equivalently,
$$
  \mathrm{ex}_3(n, K_4^3) / \binom{n}{3} \to 5/9 \text{ as } n \to \infty.
$$
Turán conjectured that the lower bound construction (partition into $3$ equal parts,
take triples with one vertex in each part or two in $X_i$ and one in $X_{i+1}$) is
optimal. This remains open. The best known upper bound is $\leq 0.5611666 \binom{n}{3}$
due to Razborov [Ra10].
-/
@[category research open, AMS 5]
theorem erdos_500 :
    Tendsto
      (fun n : ℕ => (ex3K43 n : ℝ) / (Nat.choose n 3 : ℝ))
      atTop (nhds answer(sorry)) := by
  sorry

end Erdos500
