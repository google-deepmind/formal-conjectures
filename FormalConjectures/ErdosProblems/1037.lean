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
# Erdős Problem 1037

*References:*
- [erdosproblems.com/1037](https://www.erdosproblems.com/1037)
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
-/

open Filter

namespace Erdos1037

/--
A set `s` of vertices of a graph `G` is *trivial* if the subgraph it induces is empty or
complete, that is, if `s` is an independent set or a clique of `G`.
-/
def IsTrivialSet {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  G.IsIndepSet s ∨ G.IsClique s

/--
Let $G$ be a graph on $n$ vertices in which every degree occurs at most twice, and the number of
distinct degrees is $>(\frac{1}{2}+\epsilon)n$. Must $G$ contain a trivial (empty or complete)
subgraph of size 'much larger' than $\log n$?

A question of Chen and Erdős.

The answer is no - Cambie, Chan, and Hunter have in the comment section given a simple
construction of a graph on $n$ vertices with at least $\frac{3}{4}n$ distinct degrees, every
degree appears at most twice, and the largest trivial subgraph has size $O(\log n)$.
-/
@[category research solved, AMS 5]
theorem erdos_1037 : answer(False) ↔
    ∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (∀ d : ℕ, {v : Fin n | (G.neighborSet v).ncard = d}.ncard ≤ 2) →
      ((1 / 2 + ε) * (n : ℝ) <
        ((Set.range fun v : Fin n => (G.neighborSet v).ncard).ncard : ℝ)) →
      ∃ s : Set (Fin n), IsTrivialSet G s ∧ (C * Real.log (n : ℝ) < (s.ncard : ℝ)) := by
  sorry

/--
Cambie, Chan, and Hunter have in the comment section given a simple construction of a graph on
$n$ vertices with at least $\frac{3}{4}n$ distinct degrees, every degree appears at most twice,
and the largest trivial subgraph has size $O(\log n)$.
-/
@[category research solved, AMS 5]
theorem erdos_1037.variants.cambie_chan_hunter :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      (∀ d : ℕ, {v : Fin n | (G.neighborSet v).ncard = d}.ncard ≤ 2) ∧
      (3 / 4 * (n : ℝ) ≤
        ((Set.range fun v : Fin n => (G.neighborSet v).ncard).ncard : ℝ)) ∧
      ∀ s : Set (Fin n), IsTrivialSet G s → ((s.ncard : ℝ) ≤ C * Real.log (n : ℝ)) := by
  sorry

end Erdos1037
