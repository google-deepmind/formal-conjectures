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
# Erdős Problem 833

*References:*
- [erdosproblems.com/833](https://www.erdosproblems.com/833)
- [ErLo75] Erdős, P. and Lovász, L., Problems and results on {$3$}-chromatic hypergraphs and some
  related questions. (1975), 609--627.
-/

namespace Erdos833

open Filter Asymptotics

/--
Does there exist an absolute constant $c>0$ such that, for all $r\geq 2$, in any $r$-uniform
hypergraph with chromatic number $3$ there is a vertex contained in at least $(1+c)^r$ many edges?

This was solved by Erdős and Lovász [ErLo75], who proved in particular that there is a vertex
contained in at least $\frac{2^{r-1}}{4r}$ many edges.
-/
@[category research solved, AMS 5]
theorem erdos_833 :
    answer(True) ↔ ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform r → H.HasHypergraphChromaticNumber 3 →
        ∃ v : Fin n, (1 + c) ^ r ≤ (H.hypergraphDegree v : ℝ) := by
  sorry

end Erdos833
