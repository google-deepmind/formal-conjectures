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
# Erdős Problem 1019

Does every graph on $n$ vertices with at least $\lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$
edges contain a saturated (maximal) planar subgraph on more than 3 vertices?

*Reference:* [erdosproblems.com/1019](https://www.erdosproblems.com/1019)

[Er64f] [Er69c] [Er71]
-/

open SimpleGraph Finset

namespace Erdos1019

/-- A graph is planar if it can be embedded in the plane without edge crossings.
Mathlib does not yet have a formalization of graph planarity; we axiomatize it
here as an opaque predicate. -/
opaque IsPlanar {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop

/--
Erdős Problem 1019 [Er64f, Er69c, Er71]:

Every graph on $n \geq 4$ vertices with at least
$\lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$ edges contains a maximal planar subgraph
(planar with exactly $3k - 6$ edges) on some $k > 3$ vertices.

Proved by Simonovits.
-/
@[category research solved, AMS 5]
theorem erdos_1019 :
    answer(True) ↔
    ∀ n : ℕ, n ≥ 4 →
      ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        haveI := dG;
        G.edgeFinset.card ≥ n ^ 2 / 4 + (n + 1) / 2 →
        ∃ (k : ℕ) (_ : k > 3) (H : SimpleGraph (Fin k))
          (dH : DecidableRel H.Adj) (f : Fin k → Fin n),
          haveI := dH;
          Function.Injective f ∧
          (IsPlanar H ∧ H.edgeFinset.card = 3 * k - 6) ∧
          ∀ u v, H.Adj u v → G.Adj (f u) (f v) := by
  sorry

end Erdos1019
