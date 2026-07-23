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
# Erdős Problem 579

*References:*
- [erdosproblems.com/579](https://www.erdosproblems.com/579)
- [EHSS83] P. Erdős, A. Hajnal, V. T. Sós and E. Szemerédi, *More results on Ramsey–Turán
  type problems*, Combinatorica **3** (1983), 69–81.
-/

open Classical Filter SimpleGraph

namespace Erdos579

/-- The octahedron $K_{2,2,2}$: the complete tripartite graph with all three parts of
size $2$. -/
abbrev octahedron : SimpleGraph (Σ _ : Fin 3, Fin 2) :=
  completeMultipartiteGraph (fun _ : Fin 3 => Fin 2)

/--
Let $\delta > 0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no
$K_{2,2,2}$ (the octahedron) and at least $\delta n^2$ edges, must $G$ contain an independent
set of size $\gg_\delta n$?

This is a problem of Erdős, Hajnal, Sós, and Szemerédi [EHSS83]. It is **open**; they proved
the statement for $\delta > 1/8$ (see `erdos_579.variants.ehss_large_delta`), and the
difficulty is to push the edge-density threshold down to an arbitrary $\delta > 0$.

Here $K_{2,2,2}$ is the complete tripartite graph with all parts of size $2$, encoded as
`completeMultipartiteGraph (fun _ : Fin 3 => Fin 2)`; "contains no $K_{2,2,2}$" is expressed
via `SimpleGraph.Free`.
-/
@[category research open, AMS 5]
theorem erdos_579 : answer(sorry) ↔
    ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), octahedron.Free G →
        δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          c * n ≤ (G.indepNum : ℝ) := by
  sorry

/--
The partial result of Erdős, Hajnal, Sós, and Szemerédi [EHSS83]: the statement of
`erdos_579` holds whenever the edge-density coefficient exceeds $1/8$. That is, for every
$\delta > 1/8$ there is a $c > 0$ such that for all sufficiently large $n$, every
$K_{2,2,2}$-free graph $G$ on $n$ vertices with at least $\delta n^2$ edges has an independent
set of size at least $c n$.
-/
@[category research solved, AMS 5]
theorem erdos_579.variants.ehss_large_delta (δ : ℝ) (hδ : 1 / 8 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), octahedron.Free G →
        δ * (n : ℝ) ^ 2 ≤ G.edgeFinset.card →
          c * n ≤ (G.indepNum : ℝ) := by
  sorry

/--
Sanity check that the forbidden structure is non-trivial: the octahedron is of course not
octahedron-free, since it contains a copy of itself.
-/
@[category test, AMS 5]
theorem erdos_579.variants.octahedron_not_free : ¬ octahedron.Free octahedron :=
  fun h => h IsContained.rfl

end Erdos579
