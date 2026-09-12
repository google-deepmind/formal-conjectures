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
# Erdős Problem 917

*Reference:* [erdosproblems.com/917](https://www.erdosproblems.com/917)
-/

open Filter SimpleGraph
open scoped Topology

namespace Erdos917

/-- A graph is $k$-chromatic critical if it has chromatic number $k$ and deleting any edge
decreases the chromatic number. -/
def IsKCritical {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧
    ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber < k

/-- $f_k(n)$ is the largest number of edges in a $k$-chromatic critical graph on $n$ vertices. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sSup { m | ∃ G : SimpleGraph (Fin n), IsKCritical G k ∧ G.edgeSet.ncard = m }

/--
Let $k\geq 4$ and $f_k(n)$ be the largest number of edges in a graph on $n$ vertices which has
chromatic number $k$ and is critical (i.e. deleting any edge reduces the chromatic number).
Is it true that
$$
f_k(n) \gg_k n^2?
$$
-/
@[category research open, AMS 5]
theorem erdos_917.parts.i :
    answer(sorry) ↔ ∀ k ≥ 4, ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ 2 ≤ f k n := by
  sorry

/--
Is it true that
$$
f_6(n)\sim n^2/4?
$$
-/
@[category research open, AMS 5]
theorem erdos_917.parts.ii :
    answer(sorry) ↔
      Tendsto (fun n : ℕ ↦ (f 6 n : ℝ) / n ^ 2) atTop (𝓝 ((1 : ℝ) / 4)) := by
  sorry

/--
More generally, is it true that, for $k\geq 6$,
$$
f_k(n) \sim \frac{1}{2}\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2?
$$
-/
@[category research open, AMS 5]
theorem erdos_917.parts.iii :
    answer(sorry) ↔
      ∀ k ≥ 6,
        Tendsto (fun n : ℕ ↦ (f k n : ℝ) / n ^ 2) atTop
          (𝓝 (((1 : ℝ) / 2) * (1 - 1 / ⌊(k : ℝ) / 3⌋))) := by
  sorry

end Erdos917
