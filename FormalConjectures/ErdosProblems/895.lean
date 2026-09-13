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
# Erdős Problem 895

*Reference:* [erdosproblems.com/895](https://www.erdosproblems.com/895)
-/

open Filter SimpleGraph

namespace Erdos895

/--
Is it true that, for all sufficiently large $n$, if $G$ is a triangle-free graph on
$\{1,\ldots,n\}$ then there must exist three independent points $a,b,a+b$?
-/
@[category research open, AMS 5 11]
theorem erdos_895 :
    answer(sorry) ↔
      ∀ᶠ n : ℕ in atTop,
        ∀ (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj],
          G.CliqueFree 3 →
            ∃ a b : Fin (n + 1),
              0 < a.val ∧ 0 < b.val ∧
                ∃ hle : a.val + b.val ≤ n,
                  G.IsIndepSet {a, b, ⟨a.val + b.val, Nat.lt_succ_of_le hle⟩} := by
  sorry

end Erdos895
