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
# Problem 740: Infinitary version of chromatic number and odd cycles

*Reference:* [Erdős Problems](https://erdosproblems.com/740)

Does every graph with infinite chromatic number contain a subgraph of infinite chromatic number that avoids odd cycles of length ≤r?
-/

variable {V : Type*}

/-- A graph avoids odd cycles of length ≤ r if it contains no odd cycles of length at most r -/
def avoidsOddCyclesOfLength (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (n : ℕ) (v : V) (c : G.Walk v v), c.length = n → n ≤ r → Odd n → ¬c.IsCycle

@[category research open, AMS 5]
theorem erdos_740 :
    (∀ (r : ℕ) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ →
      ∃ (H : G.Subgraph), H.coe.chromaticNumber = ⊤ ∧ avoidsOddCyclesOfLength H.coe r) ↔
    answer(sorry) := by
  sorry
