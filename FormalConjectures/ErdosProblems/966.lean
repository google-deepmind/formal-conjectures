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
# Erdős Problem 966

*References:*
- [erdosproblems.com/966](https://www.erdosproblems.com/966)
- [Er75b] Erdős, Paul, *Problems and results in combinatorial number theory*. Journées
  Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295-310.
-/

namespace Erdos966

/--
Let $k,r\geq 2$. Does there exist a set $A\subseteq \mathbb{N}$ that contains no non-trivial
arithmetic progression of length $k+1$, yet in any $r$-colouring of $A$ there must exist a
monochromatic non-trivial arithmetic progression of length $k$?

Erdős [Er75b] reported that 'Spencer has recently shown that such a sequence exists', but gives
no reference.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos966.lean"]
theorem erdos_966 : answer(True) ↔
    ∀ k r : ℕ, 2 ≤ k → 2 ≤ r → ∃ A : Set ℕ, A.IsAPOfLengthFree (k + 1) ∧
      ∀ coloring : A → Fin r, ContainsMonoAPofLength coloring k := by
  sorry

end Erdos966
