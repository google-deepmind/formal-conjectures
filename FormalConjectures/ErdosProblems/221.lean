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
# Erdős Problem 221

*References:*
- [erdosproblems.com/221](https://www.erdosproblems.com/221)
- [Lo54] Lorentz, G. G., *On a problem of additive number theory*. Proc. Amer. Math. Soc. (1954), 838-841.
- [Ru72] Ruzsa, Jr., I., *On a problem of P. Erdős*. Canad. Math. Bull. (1972), 309-310.
-/

open Filter Asymptotics

namespace Erdos221

/--
Is there a set $A\subset\mathbb{N}$ such that, for all large $N$,
\[\lvert A\cap\{1,\ldots,N\}\rvert \ll N/\log N\]
and such that every large integer can be written as $2^k+a$ for some
$k\geq 0$ and $a\in A$?

Lorentz [Lo54] proved there is such a set with, for all large $N$,
\[\lvert A\cap\{1,\ldots,N\}\rvert \ll \frac{\log\log N}{\log N}N\]
The answer is yes, proved by Ruzsa [Ru72].
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/Woett/Lean-files/blob/main/ErdosProblem221.lean"]
theorem erdos_221 :
    answer(True) ↔ ∃ A : Set ℕ,
      ((fun N => ({a ∈ A | a ≤ N}.ncard : ℝ)) ≪ (fun N => (N : ℝ) / Real.log N)) ∧
      ∀ᶠ N in atTop, ∃ k a, 0 ≤ k ∧ a ∈ A ∧ N = 2 ^ k + a := by
  sorry

end Erdos221
