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
# Erdős Problem 147

*Reference:* [erdosproblems.com/147](https://www.erdosproblems.com/147)

[ErSi84] Erdős, P. and Simonovits, M., _Cube-supersaturated graphs and related problems_,
Progress in graph theory (1984).

[Ja23] Janzer, O., _Disproof of a conjecture of Erdős and Simonovits on the Turán number_,
(2023).

[Ja23b] Janzer, O., _Disproof of a conjecture of Erdős and Simonovits on the Turán number
(the case r = 3)_, (2023).
-/

open SimpleGraph

namespace Erdos147

/-- An injective graph homomorphism from $H$ to $F$; witnesses that $F$ contains a
subgraph isomorphic to $H$. -/
def ContainsSubgraph {V U : Type*} (F : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → F.Adj (f u) (f v)

/-- The Turán number $\mathrm{ex}(n; H)$: the maximum number of edges in a simple graph on $n$
vertices that contains no copy of $H$ as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬ContainsSubgraph F H ∧ F.edgeFinset.card = m}

/--
Erdős Problem 147 [ErSi84]:
If $H$ is a bipartite graph with minimum degree $r$ (i.e., every vertex of $H$ has
degree at least $r$, where $r \geq 2$), is it true that there exists
$\varepsilon = \varepsilon(H) > 0$ such that
$$
\mathrm{ex}(n; H) \gg n^{2 - 1/(r-1) + \varepsilon}?
$$
That is, do there exist constants $C > 0$ and $N_0 \in \mathbb{N}$ such that for all $n \geq N_0$:
$$
\mathrm{ex}(n; H) \geq C \cdot n^{2 - 1/(r-1) + \varepsilon}?
$$

This conjecture was **disproved**: Janzer [Ja23] disproved it for even $r \geq 4$, and
[Ja23b] disproved it for $r = 3$, constructing for any $\delta > 0$ a $3$-regular bipartite
graph $H$ with $\mathrm{ex}(n; H) \ll n^{4/3 + \delta}$.
-/
@[category research solved, AMS 5]
theorem erdos_147 : answer(False) ↔
    ∀ (r : ℕ), 2 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      (∀ v : U, r ≤ H.degree v) →
      ∃ ε : ℝ, 0 < ε ∧
        ∃ C : ℝ, 0 < C ∧
          ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
            C * (n : ℝ) ^ ((2 : ℝ) - 1 / ((r : ℝ) - 1) + ε) ≤ (turanNumber H n : ℝ) := by
  sorry

end Erdos147
