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
- [Bl21] Bloom, T. F., On a density conjecture about unit fractions. arXiv:2112.03726 (2021).
-/

namespace Erdos47

/--
If $\delta > 0$ and $N$ is sufficiently large in terms of $\delta$, and
$A \subseteq \{1,\ldots,N\}$ is such that $\sum_{a\in A} 1/a > \delta \log N$,
then there exists $S \subseteq A$ such that $\sum_{n\in S} 1/n = 1$.

This was proved by Bloom [Bl21].
-/
@[category research solved, AMS 11,
formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/main/src/v4.30.0/ErdosProblems/Erdos47.lean#L495"]
theorem erdos_47 : answer(True) ↔
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      δ * Real.log (N : ℝ) < ∑ n ∈ A, (1 : ℝ) / n →
      ∃ S ⊆ A, ∑ n ∈ S, (1 : ℝ) / n = 1 := by
  sorry

end Erdos47
