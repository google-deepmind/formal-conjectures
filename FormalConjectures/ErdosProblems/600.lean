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
# Erdős Problem 600

*Reference:* [erdosproblems.com/600](https://www.erdosproblems.com/600)

Let $e(n, r)$ be minimal such that every graph on $n$ vertices with at least $e(n, r)$
edges, each edge contained in at least one triangle, must have an edge contained
in at least $r$ triangles. Let $r \geq 2$. Is it true that
$$e(n, r+1) - e(n, r) \to \infty$$
as $n \to \infty$? Is it true that
$$e(n, r+1) / e(n, r) \to 1$$
as $n \to \infty$?

Ruzsa and Szemerédi [RuSz78] proved that $e(n, r) = o(n^2)$ for any fixed $r$.

See also problem [80](https://www.erdosproblems.com/80).

[RuSz78] Ruzsa, I.Z. and Szemerédi, E., _Triple systems with no six points carrying
three triangles_. Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976),
Vol. II, Colloq. Math. Soc. János Bolyai 18, North-Holland, 1978, pp. 939–945.

[Er87] Erdős, P., 1987.
-/

open Filter SimpleGraph Classical

open scoped Topology

namespace Erdos600

/-- The number of triangles containing the edge $\{u, v\}$ in graph $G$:
the count of vertices $w$ with $w \neq u$, $w \neq v$, adjacent to both $u$ and $v$. -/
noncomputable def trianglesThrough {n : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => w ≠ u ∧ w ≠ v ∧ G.Adj u w ∧ G.Adj v w).card

/-- A graph is triangle-covered if every edge is contained in at least one triangle. -/
def IsTriangleCovered {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → 0 < trianglesThrough G u v

/-- $e(n, r)$: the minimal number of edges such that every triangle-covered graph
on $n$ vertices with at least that many edges has an edge in at least $r$ triangles. -/
noncomputable def erdosE (n r : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ G : SimpleGraph (Fin n),
    IsTriangleCovered G → G.edgeFinset.card ≥ m →
    ∃ u v : Fin n, G.Adj u v ∧ trianglesThrough G u v ≥ r}

/--
Erdős Problem 600, Part 1 [Er87]:

Is it true that for any $r \geq 2$, $e(n, r+1) - e(n, r) \to \infty$ as $n \to \infty$?
That is, for any bound $M$, for all sufficiently large $n$,
$e(n, r+1) \geq e(n, r) + M$.
-/
@[category research open, AMS 5]
theorem erdos_600 : answer(sorry) ↔ ∀ (r : ℕ), r ≥ 2 →
    ∀ M : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      erdosE n (r + 1) ≥ erdosE n r + M := by
  sorry

/--
Erdős Problem 600, Part 2 [Er87]:

Is it true that for any $r \geq 2$, $e(n, r+1) / e(n, r) \to 1$ as $n \to \infty$?
-/
@[category research open, AMS 5]
theorem erdos_600.variants.ratio : answer(sorry) ↔ ∀ (r : ℕ), r ≥ 2 →
    Tendsto
      (fun n : ℕ => (erdosE n (r + 1) : ℝ) / (erdosE n r : ℝ))
      atTop (nhds 1) := by
  sorry

end Erdos600
