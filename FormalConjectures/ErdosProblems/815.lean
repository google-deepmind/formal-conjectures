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
# Erdős Problem 815

*Reference:* [erdosproblems.com/815](https://www.erdosproblems.com/815)

Let $k \geq 3$ and $n$ be sufficiently large. Is it true that if $G$ is a graph
with $n$ vertices and $2n - 2$ edges such that every proper induced subgraph has
minimum degree $\leq 2$ then $G$ must contain a copy of $C_k$?

Such graphs are called *degree 3 critical*. This conjecture was **disproved** by
Narins, Pokrovskiy, and Szabó [NPS17], who proved that there exist arbitrarily
large such graphs with no cycle of length $23$.

It remains open whether the answer is affirmative when restricted to even $k$.

[NPS17] Narins, L., Pokrovskiy, A. and Szabó, T., _Graphs without long cycles_, 2017.
-/

open Filter SimpleGraph

namespace Erdos815

/-- A graph on `Fin n` is *degree 3 critical* if it has $2n - 2$ edges and every
    proper induced subgraph has a vertex of degree at most $2$. -/
noncomputable def IsDegree3Critical {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.edgeSet.ncard = 2 * n - 2 ∧
  ∀ S : Finset (Fin n), S.Nonempty → S ⊂ Finset.univ →
    ∃ v ∈ S, ((↑S : Set (Fin n)) ∩ G.neighborSet v).ncard ≤ 2

/--
**Erdős Problem 815** (disproved by Narins–Pokrovskiy–Szabó [NPS17]):

Is it true that for every $k \geq 3$, every sufficiently large degree 3
critical graph contains a cycle of length $k$? The answer is **no**.
-/
@[category research solved, AMS 5]
theorem erdos_815 : answer(False) ↔
    ∀ k : ℕ, k ≥ 3 → ∀ᶠ n in atTop,
      ∀ (G : SimpleGraph (Fin n)), IsDegree3Critical G →
        ∃ (v : Fin n) (p : G.Walk v v), p.IsCycle ∧ p.length = k := by
  sorry

end Erdos815
