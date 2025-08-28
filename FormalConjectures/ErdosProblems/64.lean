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
# Erdős Problem 64

*Reference:* [erdosproblems.com/64](https://www.erdosproblems.com/64)
-/

namespace Erdos64

/--
Does every finite graph with minimum degree at least $3$
contain a cycle of length $2^k$ for some $k \geq 2$?
-/
@[category research open, AMS 5]
theorem erdos_64 :
    (∀ (V : Type*) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
        G.minDegree ≥ 3 → ∃ (k : ℕ) (v : V) (c : G.Walk v v),
            k ≥ 2 ∧ c.IsCycle ∧ c.length = 2^k) ↔ answer(sorry) := by
  sorry

-- TODO(firsching): add more context

end Erdos64
