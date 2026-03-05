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
# Erdős Problem 641

*Reference:* [erdosproblems.com/641](https://www.erdosproblems.com/641)

A problem of Erdős and Hajnal on chromatic number and edge-disjoint cycles.

[Er92b] Erdős, P., problems in combinatorics.

[Er97d] Erdős, P., some of my favourite problems, p.84.

[JSS24] Janzer, O., Steiner, R., and Sudakov, B., disproof of the conjecture.
-/

open SimpleGraph

namespace Erdos641

/--
**Erdős Problem 641** (Original conjecture, DISPROVED) [Er92b][Er97d, p.84]:

Is there some function $f$ such that for all $k \geq 1$, if a finite graph $G$ has
chromatic number $\geq f(k)$ then $G$ has $k$ edge-disjoint cycles on the same set
of vertices?

This was resolved in the negative by Janzer, Steiner, and Sudakov [JSS24] —
in fact, this fails even at $k = 2$.
-/
@[category research solved, AMS 5]
theorem erdos_641 : answer(False) ↔
    ∀ k : ℕ, 1 ≤ k →
      ∃ f : ℕ,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          (f : ℕ∞) ≤ G.chromaticNumber →
          ∃ (cycles : Fin k → Σ (v : Fin n), G.Walk v v),
            (∀ i, (cycles i).2.IsCycle) ∧
            (∀ i j, (cycles i).2.support.toFinset = (cycles j).2.support.toFinset) ∧
            (∀ i j, i ≠ j →
              Disjoint (cycles i).2.edges.toFinset (cycles j).2.edges.toFinset) := by
  sorry

/--
**Erdős Problem 641** (Disproof, Janzer–Steiner–Sudakov [JSS24]):

There exists $k \geq 1$ such that for any proposed bound $f$, one can find a
finite graph with chromatic number at least $f$ but without $k$ edge-disjoint
cycles on any common vertex set. In fact $k = 2$ already fails.
-/
@[category research solved, AMS 5]
theorem erdos_641.variants.disproof :
    ∃ k : ℕ, 1 ≤ k ∧
      ∀ f : ℕ,
        ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
          (f : ℕ∞) ≤ G.chromaticNumber ∧
          ¬∃ (cycles : Fin k → Σ (v : Fin n), G.Walk v v),
            (∀ i, (cycles i).2.IsCycle) ∧
            (∀ i j, (cycles i).2.support.toFinset = (cycles j).2.support.toFinset) ∧
            (∀ i j, i ≠ j →
              Disjoint (cycles i).2.edges.toFinset (cycles j).2.edges.toFinset) := by
  sorry

end Erdos641
