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
# Problem 108: Erdős-Hajnal conjecture on subgraphs with high girth and chromatic number

*Reference:* [Erdős Problems](https://erdosproblems.com/108)

For every r≥4 and k≥2, does there exist finite f(k,r) such that every graph of chromatic number ≥f(k,r) contains a subgraph of girth ≥r and chromatic number ≥k?
-/

variable {V : Type*} [Fintype V]

@[category research open, AMS 05]
theorem erdos_108 :
    (∀ (r k : ℕ), r ≥ 4 → k ≥ 2 →
      ∃ (f : ℕ → ℕ → ℕ), ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        G.chromaticNumber ≥ f k r →
        ∃ (H : G.Subgraph), H.coe.girth ≥ r ∧ H.coe.chromaticNumber ≥ k) ↔
    answer(sorry) := by
  sorry
