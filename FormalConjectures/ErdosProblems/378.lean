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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 378

*References:*
- [erdosproblems.com/378](https://www.erdosproblems.com/378)
-/

@[expose] public section

open Filter Topology MeasureTheory SimpleGraph

namespace Erdos378

/-- The number of squarefree binomial coefficients in the interior of row $n$. -/
noncomputable def squarefreeCount (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico 1 n).filter fun k => Squarefree (n.choose k)).card

/-- For every nonnegative integer $r$, the integers $n$ with at least $r$ squarefree
interior binomial coefficients have a natural density, and this density is positive.
This follows from Granville and Ramaré [GrRa96]. -/
@[category research solved, question, AMS 11]
theorem erdos_378 (r : ℕ) : {n : ℕ | r ≤ squarefreeCount n}.HasPosDensity := by
  sorry

end Erdos378
