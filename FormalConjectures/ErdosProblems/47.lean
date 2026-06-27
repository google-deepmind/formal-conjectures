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
# Erdős Problem 47

*References:*
- [erdosproblems.com/47](https://www.erdosproblems.com/47)
- [Bl21] Bloom, T. F., *On a density conjecture about unit fractions*. arXiv:2112.03726
  (2021).
- [LiSa24] Liu, Y. and Sawhney, M., *On further questions regarding unit fractions*.
  arXiv:2404.07113 (2024).
-/

namespace Erdos47

open Filter
open scoped BigOperators

/-- The reciprocal sum of a finite set of natural numbers. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (1 : ℝ) / a

/--
If $\delta>0$ and $N$ is sufficiently large in terms of $\delta$, and $A\subseteq\{1,\ldots,N\}$ is such that $\sum_{a\in A}\frac{1}{a}>\delta \log N$ then must there exist $S\subseteq A$ such that $\sum_{n\in S}\frac{1}{n}=1$?

Bloom [Bl21] proved this in the affirmative.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos47.lean"]
theorem erdos_47 : answer(True) ↔
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      δ * Real.log (N : ℝ) < reciprocalSum A →
      ∃ S : Finset ℕ, S ⊆ A ∧ reciprocalSum S = 1 := by
  sorry

end Erdos47
