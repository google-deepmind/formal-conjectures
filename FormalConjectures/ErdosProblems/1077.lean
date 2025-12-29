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

/-!
# Erdős Problem 1077

*Reference:* [erdosproblems.com/1077](https://www.erdosproblems.com/1077)
-/

open Classical Finset Filter SimpleGraph

namespace Erdos1077

/--
We call a graph $D$-balanced (or $D$-almost-regular) if the maximum degree is at most $D$ times the
minimum degree.

Let $ε, α > 0$ and $D$ and $n$ be sufficiently large. If $G$ is a graph on $n$ vertices with at
least $n^{1+α}$ edges, then must $G$ contain a $D$-balanced subgraph on $m > n^{1-α}$ vertices with
at least $εm^{1+α}$ edges?
-/
@[category research solved, AMS 5]
theorem erdos_1077 :
    (∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 → ∀ᶠ D in atTop, ∀ᶠ n in atTop,
      ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
        ∃ (H : Subgraph G),
          letI m := H.verts.ncard
          IsBalanced H.coe D ∧
          m > (n : ℝ) ^ (1 - α) ∧
          H.edgeSet.ncard > ε * m ^ (1 + α))
      ↔ answer(sorry) := by
  sorry

end Erdos1077
