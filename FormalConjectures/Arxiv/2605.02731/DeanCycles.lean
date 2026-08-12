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
# Dean's conjecture on cycles of length divisible by `k`

*References:*
- [arxiv/2605.02731](https://arxiv.org/abs/2605.02731)
  **Existence of cycles of length divisible by 3 or 4**
  by *Ilkyoo Choi, Hojin Chu, Ringi Kim, Boram Park*, where this is Conjecture 1.1.
- [De88] Dean, N., Open problem, in Cycles and Rays. (1988).
- [DeLeSa93] Dean, N. and Lesniak, L. and Saito, A., Cycles of length 0 modulo 4 in graphs.
  Discrete Math. (1993), 133--139.
- [ChSa94] Chen, G. and Saito, A., Graphs with a cycle of length divisible by three.
  J. Combin. Theory Ser. B (1994), 277--292.
-/

open SimpleGraph

namespace Arxiv.«2605.02731»

/--
**Conjecture 1.1 (Dean, 1988).** For every integer $k \geq 3$, every finite simple graph with
minimum degree at least $k$ contains a cycle whose length is divisible by $k$.

A cycle has length at least `3`, so the divisor is never `0` and the statement is not
satisfied for a trivial reason. `SimpleGraph.minDegree` is `0` on a graph with no vertices and
on a graph with no edges, so the hypothesis excludes both.
-/
@[category research open, AMS 5]
theorem dean_conjecture :
    answer(sorry) ↔ ∀ (k : ℕ), 3 ≤ k → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], k ≤ G.minDegree →
        ∃ m ∈ G.cycleLengths, k ∣ m := by
  sorry

/--
The case $k = 5$. This is the only case of the conjecture that is still open.
-/
@[category research open, AMS 5]
theorem dean_conjecture.variants.five :
    answer(sorry) ↔ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], 5 ≤ G.minDegree → ∃ m ∈ G.cycleLengths, 5 ∣ m := by
  sorry

/--
The case $k = 3$, proved by Chen and Saito [ChSa94].
-/
@[category research solved, AMS 5]
theorem dean_conjecture.variants.three {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : 3 ≤ G.minDegree) :
    ∃ m ∈ G.cycleLengths, 3 ∣ m := by
  sorry

/--
The case $k = 4$, proved by Dean, Lesniak and Saito [DeLeSa93].
-/
@[category research solved, AMS 5]
theorem dean_conjecture.variants.four {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : 4 ≤ G.minDegree) :
    ∃ m ∈ G.cycleLengths, 4 ∣ m := by
  sorry

/--
The cases $k \geq 6$, proved by Liu, Ma and Zhao (2026). With [ChSa94] and [DeLeSa93] this
leaves `dean_conjecture.variants.five` as the only open case.
-/
@[category research solved, AMS 5]
theorem dean_conjecture.variants.six_le {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}
    (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    ∃ m ∈ G.cycleLengths, k ∣ m := by
  sorry

/-- A graph with no edges has minimum degree `0`, so the hypothesis of the conjecture rules it
out. This is a check that the hypothesis carries weight. -/
@[category test, AMS 5]
theorem minDegree_bot_eq_zero : (⊥ : SimpleGraph (Fin 5)).minDegree = 0 := by
  decide

/-- The complete graph on four vertices has minimum degree `3`, so it is one of the graphs the
case `k = 3` applies to. -/
@[category test, AMS 5]
theorem minDegree_top_fin_four : (⊤ : SimpleGraph (Fin 4)).minDegree = 3 := by
  decide

end Arxiv.«2605.02731»
