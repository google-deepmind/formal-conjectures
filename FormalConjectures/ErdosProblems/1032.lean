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
# Erdős Problem 1032

*Reference:* [erdosproblems.com/1032](https://www.erdosproblems.com/1032)
-/

namespace Erdos1032

open SimpleGraph

/--
A graph is $4$-chromatic critical if it has chromatic number $4$, and removing any edge decreases
the chromatic number to $3$.
-/
def IsFourChromaticCritical {V : Type*} (G : SimpleGraph V) : Prop :=
  G.chromaticNumber = 4 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber = 3

open scoped Classical in
/--
We say that a graph is $4$-chromatic critical if it has chromatic number $4$, and removing any
edge decreases the chromatic number to $3$.

Is there, for arbitrarily large $n$, a $4$-chromatic critical graph on $n$ vertices with minimum
degree $\gg n$?
-/
@[category research open, AMS 5]
theorem erdos_1032 : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ N : ℕ, ∃ n ≥ N, ∃ G : SimpleGraph (Fin n),
      IsFourChromaticCritical G ∧ c * n ≤ G.minDegree := by
  sorry

end Erdos1032
