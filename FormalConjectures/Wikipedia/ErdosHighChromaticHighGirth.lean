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
# Erdős 1959: graphs of large chromatic number and large girth

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Probabilistic_method)
* [Er59] Erdős, P. (1959). "Graph theory and probability." *Canad. J. Math.* 11, pp. 34--38.
* [AlSp16] Alon, N. and Spencer, J. (2016). *The Probabilistic Method* (4th ed.), §3.3.
-/

open Classical SimpleGraph

namespace ErdosHighChromaticHighGirth

/- ## Chromatic number and girth

Both `SimpleGraph.chromaticNumber` (valued in `ℕ∞`) and `SimpleGraph.girth` (valued in `ℕ`,
with `0` when the graph is acyclic) are provided by Mathlib. We work with both as given. -/

/--
**Erdős 1959.** For every integers `k ≥ 2` and `g ≥ 3`, there exists a finite simple graph
`G` with chromatic number at least `k` and girth at least `g`.

We use `Fintype.card V = n` for existence of a vertex set and `ℕ∞`-valued
`SimpleGraph.chromaticNumber`. The girth bound `g ≤ G.girth` automatically implies `G` has at
least one cycle (otherwise `G.girth = 0 < g ≥ 3`), so we are not in the degenerate acyclic
regime.

**Proof status.** Deferred; see module docstring for the probabilistic-method outline from
[Er59].
-/
@[category research solved, AMS 5]
theorem erdos_1959_chromatic_girth (k g : ℕ) (hk : 2 ≤ k) (hg : 3 ≤ g) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      (k : ℕ∞) ≤ G.chromaticNumber ∧ g ≤ G.girth := by
  -- Erdős 1959 [Er59]. Probabilistic method + alteration. Deferred.
  sorry

/- ## Special cases and easy corollaries -/

/--
**Case `g = 3`: graphs of arbitrarily high chromatic number with girth `≥ 3`** (i.e. no
requirement on girth, since every non-empty graph with at least one edge has girth `≥ 3`).

Here the content is just "for every `k ≥ 2` there is a graph with chromatic number `≥ k`",
which is trivially witnessed by `K_k` (chromatic number exactly `k`, girth `3` when `k ≥ 3`,
and no cycles when `k ≤ 2` so the girth condition is still satisfied vacuously for `k ≤ 2`
only — but we assume `k ≥ 2` here, which gives chromatic number `≥ 2` in any graph with an
edge).

We extract this as a thin wrapper around the main theorem rather than proving it directly:
the main theorem immediately specialises to `g = 3`, so there is nothing to prove. The corollary
is still useful as a "wake-up" special case — though even for `g = 3` the direct route is via
`completeGraph (Fin k)` and not via the probabilistic method.
-/
@[category research solved, AMS 5]
theorem erdos_1959_chromatic_girth_three (k : ℕ) (hk : 2 ≤ k) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      (k : ℕ∞) ≤ G.chromaticNumber ∧ 3 ≤ G.girth :=
  erdos_1959_chromatic_girth k 3 hk (le_refl 3)

/--
**Case `k = 2`: graphs of arbitrary girth with chromatic number `≥ 2`.**

A graph has chromatic number `≥ 2` iff it has at least one edge. Any even cycle `C_{2g}`
(length-`2g` cycle) has chromatic number exactly `2` and girth exactly `2g`, hence girth
`≥ g`. So this special case is elementary and does not need the probabilistic method.

We record it as a specialisation of the main theorem.
-/
@[category research solved, AMS 5]
theorem erdos_1959_chromatic_girth_two_chromatic (g : ℕ) (hg : 3 ≤ g) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      (2 : ℕ∞) ≤ G.chromaticNumber ∧ g ≤ G.girth :=
  erdos_1959_chromatic_girth 2 g (le_refl 2) hg

/- ## Associated quantitative form

Erdős's original 1959 theorem gives an explicit growth rate: for every `k, g` one can take
`n = n(k, g)` polynomial in `k` and in `2^g`. The explicit bound has been refined by many
authors (notably Nešetřil–Rödl for explicit constructions), but the *existence* statement
above is the canonical form.

We omit a quantitative version. -/

end ErdosHighChromaticHighGirth
