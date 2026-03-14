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
# Erdős Problem 740: Infinitary version of chromatic number and odd cycles

*Reference:* [erdosproblems.com/740](https://erdosproblems.com/740)
-/

namespace Erdos740

/-- A graph avoids odd cycles of length $≤ r$ if it contains no odd cycles of length at most $r$. -/
def NoShortOddCycle {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → Odd c.length → c.length > r

/--
Does every graph $G$ with $\chi(G) = \infty$ contain, for every $r \in \mathbb{N}$, a subgraph
$H \subseteq G$ such that $\chi(H) = \infty$ and $H$ contains no odd cycle of length $\le r$?
-/
@[category research open, AMS 5]
theorem erdos_740 :
    answer(sorry) ↔
      ∀ (V : Type*) (r : ℕ) (G : SimpleGraph V),
        G.chromaticNumber = ⊤ →
          ∃ (H : G.Subgraph), H.coe.chromaticNumber = ⊤ ∧ NoShortOddCycle H.coe r := by
  sorry

-- TODO: add the related infinitary chromatic-number statements from erdosproblems.com.

end Erdos740
