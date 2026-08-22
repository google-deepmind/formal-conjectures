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
# Erdős Problem 279
*Reference:* [erdosproblems.com/279](https://www.erdosproblems.com/279)
-/

namespace Erdos279

/--
Let $k\geq 3$. Is there a choice of congruence classes $a_p\pmod{p}$ for every prime $p$
such that all sufficiently large integers can be written as $a_p+tp$ for some prime $p$
and integer $t\geq k$?

This was formally proved in Lean by Wanfang Chen.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/WanfangChen/Erdos/blob/585b714d5146fc12926dbff54bc0afd765452481/Erdos279/DeepMindBridge.lean"]
theorem erdos_279 : answer(True) ↔ ∀ k : Nat, k ≥ 3 →
    ∃ a : Nat → Nat, ∃ N : Nat, (∀ p : Nat, p.Prime → a p < p) ∧
    ∀ n ≥ N, ∃ p : Nat, ∃ t ≥ k, p.Prime ∧ n = a p + t * p := by
  sorry

end Erdos279
