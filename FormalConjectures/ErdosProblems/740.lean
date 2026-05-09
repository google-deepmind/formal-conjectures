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
# Erdős Problem 740: Infinitary version of chromatic number and odd cycles

*Reference:* [erdosproblems.com/740](https://erdosproblems.com/740)
-/

open scoped Cardinal

namespace Erdos740

/-- A graph avoids odd cycles of length $\leq r$ if it contains no odd cycles of length at most $r$. -/
def NoShortOddCycle {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → Odd c.length → c.length > r

/--
Let $\mathfrak{m}$ be an infinite cardinal and $G$ be a graph with chromatic number $\mathfrak{m}$.
Let $r\geq 1$. Must $G$ contain a subgraph of chromatic number $\mathfrak{m}$ which does not contain
any odd cycle of length $\leq r$?
-/
@[category research open, AMS 5]
theorem erdos_740 :
    answer(sorry) ↔
      ∀ (V : Type*) (G : SimpleGraph V),
        ℵ₀ ≤ G.chromaticCardinal →
          ∀ (r : ℕ),
            ∃ (H : G.Subgraph), H.coe.chromaticCardinal = G.chromaticCardinal ∧
              NoShortOddCycle H.coe r := by
  sorry

-- TODO: add the related infinitary chromatic-number statements from erdosproblems.com.

end Erdos740
