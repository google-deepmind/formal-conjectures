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
# Erdős Problem 836

*References:*
- [erdosproblems.com/836](https://www.erdosproblems.com/836)
- [ErLo75] Erdős, P. and Lovász, L., Problems and results on {$3$}-chromatic hypergraphs and some
  related questions. (1975), 609--627.
-/

namespace Erdos836

open Filter Asymptotics

/--
Let $r\geq 2$ and let $G$ be an intersecting $r$-uniform hypergraph with chromatic number
$3$. Must $G$ contain $O(r^2)$ many vertices? Vertices are counted in the union of the edges,
so isolated vertices are excluded.

Alon has provided a counterexample to the first question: this hypergraph is intersecting,
its chromatic number is $3$, and it has $\asymp 4^r/\sqrt{r}$ many vertices.
-/
@[category research solved, AMS 5]
theorem erdos_836.parts.i :
    answer(False) ↔ ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform r → H.HasHypergraphChromaticNumber 3 → (H : Set (Finset (Fin n))).Intersecting →
        ((H.biUnion id).card : ℝ) ≤ C * (r : ℝ) ^ 2 := by
  sorry

/--
In an intersecting $r$-uniform hypergraph with chromatic number $3$, must there be two
distinct edges which meet in $\gg r$ many vertices?
-/
@[category research open, AMS 5]
theorem erdos_836.parts.ii :
    answer(sorry) ↔ ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform r → H.HasHypergraphChromaticNumber 3 → (H : Set (Finset (Fin n))).Intersecting →
        ∃ e ∈ H, ∃ f ∈ H, e ≠ f ∧ c * r ≤ ((e ∩ f).card : ℝ) := by
  sorry

end Erdos836
