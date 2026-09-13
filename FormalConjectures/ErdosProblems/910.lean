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
# Erdős Problem 910

*References:*
- [erdosproblems.com/910](https://www.erdosproblems.com/910)
- [Ru58] Rudin, M. E., *A connected subset of the plane*. Fund. Math. (1958), 15--24.
-/

open Cardinal
open scoped EuclideanGeometry Cardinal

namespace Erdos910

/--
Does every connected set in $\mathbb{R}^n$ contain a connected subset which is not a point and not
homeomorphic to the original set?

Asked by Erdős in the 1940s, who thought the answer to both questions is yes. The answer to both is
in fact no, as shown by Rudin [Ru58] (conditional on the continuum hypothesis).
-/
@[category research solved, AMS 54]
theorem erdos_910.parts.i : answer(False) ↔
    ∀ (n : ℕ) (s : Set (ℝ^n)),
      IsConnected s → s.Nontrivial →
        ∃ t : Set (ℝ^n), t ⊆ s ∧ IsConnected t ∧ t.Nontrivial ∧ IsEmpty (t ≃ₜ s) := by
  sorry

/--
If $n\geq 2$ does every connected set in $\mathbb{R}^n$ contain more than $2^{\aleph_0}$ many
connected subsets?

Asked by Erdős in the 1940s, who thought the answer to both questions is yes. The answer to both is
in fact no, as shown by Rudin [Ru58] (conditional on the continuum hypothesis).
-/
@[category research solved, AMS 54]
theorem erdos_910.parts.ii : answer(False) ↔
    ∀ (n : ℕ), 2 ≤ n → ∀ s : Set (ℝ^n),
      IsConnected s → s.Nontrivial →
        𝔠 < #{t : Set (ℝ^n) | t ⊆ s ∧ IsConnected t} := by
  sorry

end Erdos910
