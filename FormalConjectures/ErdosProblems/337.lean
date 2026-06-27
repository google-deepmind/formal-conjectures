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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 337

*References:*
- [erdosproblems.com/337](https://www.erdosproblems.com/337)
- [RT85] Ruzsa, I. Z. and Turj\'{a}nyi, S., *A note on additive bases of
  integers*. Publ. Math. Debrecen (1985), 101-104.
- [Tu84] Turj\'{a}nyi, S., *A note on basis sequences*. Topics in classical
  number theory, Vol. I, II (Budapest, 1981) (1984), 1571-1576.
-/

namespace Erdos337

open Filter Asymptotics
open scoped Pointwise

/-- The counting function $\lvert A\cap \{1,\ldots,N\}\rvert$. -/
noncomputable def countInRange (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card

/--
Let $A\subseteq \mathbb{N}$ be an additive basis (of any finite order) such that $\lvert A\cap \{1,\ldots,N\}\rvert=o(N)$. Is it true that\[\lim_{N\to \infty}\frac{\lvert (A+A)\cap \{1,\ldots,N\}\rvert}{\lvert A\cap \{1,\ldots,N\}\rvert}=\infty?\]

Turj\'{a}nyi [Tu84] answered this in the negative.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos337.lean"]
theorem erdos_337 : answer(False) ↔
    ∀ A : Set ℕ, A.IsAsymptoticAddBasis →
      (fun N : ℕ => (countInRange A N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)) →
      Tendsto
        (fun N : ℕ => (countInRange (A + A) N : ℝ) / (countInRange A N : ℝ))
        atTop atTop := by
  sorry

end Erdos337
