/-
Copyright 2025 The Formal Conjectures Authors.

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
import FormalConjectures.WrittenOnTheWallII.GraphConjecture315

/-!
# Written on the Wall II - Conjecture 291

**Verbatim statement (WOWII #291, status O):**
> If G is a simple connected graph such that n(G)> 2, then γ_t(G) ≤ k + frequency t_min(v), where k is the first step in which a zero appears in the Havil-Hakimi process.

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj291


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

For a vertex `v` in a graph `G`, **T(v)** is the number of triangles (3-cliques) incident
to `v`, i.e., the number of 3-element cliques in `G` that contain `v`.

The **triangle-frequency of the minimum** is the number of vertices that achieve the
minimum value of T(v).

**k** is the **first step in the Havel–Hakimi process at which a zero appears**.
Concretely, starting from the descending degree sequence `s₀` of `G`, we set
`s_{i+1} = havelHakimiStep s_i` and let `k` be the least `i ≥ 0` such that
`s_i` contains a zero entry (or, vacuously, has been emptied entirely). Since
each step is sorted descending and never increases entries, this is equivalent
to the last (smallest) entry of `s_i` being `0`, or `s_i` being `[]`.

This is **strictly weaker** than `n - residue(G)` (the previous, incorrect,
formalisation): `n - residue(G)` is the *total* number of reduction steps until
*every* entry is zero, whereas `k` only requires that *some* entry has hit
zero — and a 0 typically appears well before the all-zero state is reached.

**Conjecture 291:** For a simple connected graph `G` with `n > 2`,
`γ_t(G) ≤ k + frequency(t_min(v))`
where `γ_t(G)` is the total domination number, `k` is the Havel-Hakimi zero step,
and `frequency(t_min(v))` is the number of vertices achieving the minimum triangle count.
-/

namespace WrittenOnTheWallII.GraphConjecture291

open Classical SimpleGraph WrittenOnTheWallII.GraphConjecture315

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The number of triangles (3-cliques) in `G` that are incident to vertex `v`.
This is the number of 3-element cliques containing `v`. -/
noncomputable def numTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card

/-- The minimum number of triangles incident to any vertex, over all vertices of `G`. -/
noncomputable def minTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (numTrianglesAtVertex G)

/-- The number of vertices achieving the minimum triangle count. -/
noncomputable def freqMinTriangles (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun v => numTrianglesAtVertex G v = minTrianglesAtVertex G)).card

/-- The descending degree sequence of `G`, used as the starting point of the
Havel-Hakimi reduction. -/
noncomputable def descDegreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.image (fun v : α => G.degree v)).sort (· ≥ ·)

/-- The Havel-Hakimi sequence of iterates: `s i` is the result of applying
`havelHakimiStep` `i` times to the descending degree sequence of `G`. -/
noncomputable def havelHakimiIterate (G : SimpleGraph α) [DecidableRel G.Adj] (i : ℕ) :
    List ℕ :=
  (havelHakimiStep)^[i] (descDegreeSequence G)

/-- The first step `i` (counting from `0`) at which a zero appears in the
Havel-Hakimi reduction of the descending degree sequence of `G`, or in which
the sequence has been emptied. We use `sInf` over the set of such `i` so the
definition is well-defined for every graph: in particular, when `G` is a
connected graph with `n ≥ 2` the minimum degree at iteration `0` is at least
`1`, so the first zero only appears at some `i ≥ 1`; and since each step
strictly shortens the list (or empties it), at the latest by `i = n` the
sequence is empty and the predicate holds vacuously.

This is the WOWII `k` of Conjecture 291, which is the **first** step at which a
zero appears — typically strictly less than `n - residue(G)` (which is the
*total* number of reduction steps to reach the all-zero state). -/
noncomputable def havelHakimiZeroStep (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sInf {i | 0 ∈ havelHakimiIterate G i ∨ havelHakimiIterate G i = []}

/--
WOWII [Conjecture 291](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G` with `n > 2`,
`γ_t(G) ≤ k + frequency(t_min(v))`
where:
- `γ_t(G)` is the total domination number,
- `k` is the first step in which a zero appears in the Havel-Hakimi process,
- `frequency(t_min(v))` is the number of vertices achieving the minimum triangle count.
-/
@[category research open, AMS 5]
theorem conjecture291 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hn : 2 < Fintype.card α) :
    G.totalDominationNumber ≤
    havelHakimiZeroStep G + freqMinTriangles G := by
  sorry

-- Sanity checks

/-- In `K₃`, every vertex is in exactly 1 triangle. -/
@[category test, AMS 5]
example : numTrianglesAtVertex (⊤ : SimpleGraph (Fin 3)) (0 : Fin 3) = 1 := by
  unfold numTrianglesAtVertex
  decide +native

/-- In the path `P₃`, vertex 1 has no triangles incident to it
(0 and 2 are neighbors of 1 but not adjacent to each other). -/
@[category test, AMS 5]
example : numTrianglesAtVertex
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) (1 : Fin 3) = 0 := by
  unfold numTrianglesAtVertex
  decide +native

/-- In `K₃`, the minimum triangle count is 1 (every vertex has 1 triangle). -/
@[category test, AMS 5]
example : minTrianglesAtVertex (⊤ : SimpleGraph (Fin 3)) = 1 := by
  unfold minTrianglesAtVertex numTrianglesAtVertex
  decide +native

/-- `havelHakimiZeroStep` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : 0 ≤ havelHakimiZeroStep G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture291
