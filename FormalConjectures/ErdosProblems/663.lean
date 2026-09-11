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
# Erdős Problem 663

*References:*
- [erdosproblems.com/663](https://www.erdosproblems.com/663)
- [BEGL96] Burr, S. A., Erdős, P., Graham, R. L., and Li, W. W.-C.,
  *Complete sequences of sets of integer powers*. Acta Arith. (1996), 133–138.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*.
  Math. Japon. (1997), 527–537.
-/

namespace Erdos663

open Filter Asymptotics
open scoped BigOperators

/-- Let $k \geq 2$, and let $q(n,k)$ denote the least prime which does not divide
$\prod_{1 \leq i \leq k}(n+i)$. Is it true that, if $k$ is fixed and $n$ is sufficiently
large, then $q(n,k) < (1+o(1))\log n$? -/
@[category research open, AMS 11]
theorem erdos_663 : answer(sorry) ↔ ∀ k ≥ 2, ∃ error : ℕ → ℝ,
    error =o[atTop] (fun _ ↦ (1 : ℝ)) ∧ ∀ᶠ n in atTop,
      let P : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)
      ∃ q : ℕ, q.Prime ∧ ¬ q ∣ P ∧ (∀ p : ℕ, p.Prime → ¬ p ∣ P → q ≤ p) ∧
        (q : ℝ) < (1 + error n) * Real.log n := by
  sorry

-- TODO: Formalize the easy bound $q(n,k) < (1+o(1))k\log n$ recorded in the source.

end Erdos663
