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
# Erdős Problem 1068

*Reference:* [erdosproblems.com/1068](https://www.erdosproblems.com/1068)
-/

open Cardinal SimpleGraph

namespace Erdos1068

/--
Does every graph with chromatic number $\aleph_1$ contain a countable subgraph which is
infinitely connected?
-/
@[category research open, AMS 5]
theorem erdos_1068 : answer(sorry) ↔
    ∀ (V : Type) (G : SimpleGraph V), G.chromaticNumber = aleph 1 →
      ∃ s : Set V, s.Countable ∧ InfinitelyConnected (G.induce s) := by
  sorry

end Erdos1068
