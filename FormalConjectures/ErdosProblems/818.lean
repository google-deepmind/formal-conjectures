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
# Erdős Problem 818

*References:*
- [erdosproblems.com/818](https://www.erdosproblems.com/818)
- [So09d] Solymosi, József, *Bounding multiplicative energy by the sumset*. Adv. Math. (2009),
  402-408.
-/

open scoped Pointwise

namespace Erdos818

/--
Let $A$ be a finite set of integers such that $\lvert A+A\rvert \ll \lvert A\rvert$. Is it true that
\[\lvert AA\rvert \gg \frac{\lvert A\rvert^2}{(\log \lvert A\rvert)^C}\]
for some constant $C>0$?

This was proved by Solymosi [So09d], in the strong form
\[\lvert AA\rvert \gg \frac{\lvert A\rvert^2}{\log \lvert A\rvert}.\]
See also [52].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos818.lean"]
theorem erdos_818 : answer(True) ↔
    ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ A : Finset ℤ, 2 ≤ A.card → ((A + A).card : ℝ) ≤ K * (A.card : ℝ) →
        c * (A.card : ℝ) ^ 2 / (Real.log (A.card : ℝ)) ^ C ≤ ((A * A).card : ℝ) := by
  sorry

/--
This was proved by Solymosi [So09d], in the strong form
\[\lvert AA\rvert \gg \frac{\lvert A\rvert^2}{\log \lvert A\rvert}.\]
-/
@[category research solved, AMS 5 11]
theorem erdos_818.variants.solymosi :
    ∀ K : ℝ, 0 < K → ∃ c : ℝ, 0 < c ∧
      ∀ A : Finset ℤ, 2 ≤ A.card → ((A + A).card : ℝ) ≤ K * (A.card : ℝ) →
        c * (A.card : ℝ) ^ 2 / Real.log (A.card : ℝ) ≤ ((A * A).card : ℝ) := by
  sorry

end Erdos818
