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
# Erdős Problem 580

If at least half the vertices of an $n$-vertex graph have degree at least $n/2$, must the graph
contain every tree on at most $n/2$ vertices as a subgraph?

*Reference:* [erdosproblems.com/580](https://www.erdosproblems.com/580)

[EFLS95] Erdős, P., Füredi, Z., Loebl, M., and Sós, V.T.

[AKS95] Ajtai, M., Komlós, J., and Szemerédi, E.

[Zh11] Zhao, Y.
-/

open SimpleGraph Finset

namespace Erdos580

/-- An injective graph homomorphism from $H$ to $G$; witnesses that $G$ contains a
copy of $H$ as a subgraph. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős-Füredi-Loebl-Sós Conjecture (Problem 580):
Let $G$ be a graph on $n$ vertices such that at least $n/2$ vertices have degree at
least $n/2$. Must $G$ contain every tree on at most $n/2$ vertices?

Conjectured by Erdős, Füredi, Loebl, and Sós [EFLS95].
Ajtai, Komlós, and Szemerédi [AKS95] proved an asymptotic version.
Zhao [Zh11] proved the conjecture for all sufficiently large $n$.
-/
@[category research open, AMS 5]
theorem erdos_580 : answer(sorry) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      n / 2 ≤ (Finset.univ.filter (fun v => n / 2 ≤ G.degree v)).card →
      ∀ (k : ℕ) (T : SimpleGraph (Fin k)) [DecidableRel T.Adj],
        k ≤ n / 2 → T.IsTree → ContainsSubgraph G T := by
  sorry

end Erdos580
