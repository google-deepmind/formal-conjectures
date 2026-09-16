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
# Erdős Problem 296

*References:*
- [erdosproblems.com/296](https://www.erdosproblems.com/296)
- [Bl21] Bloom, T. F., *On a density conjecture about unit fractions*.
  arXiv:2112.03726 (2021).
-/

namespace Erdos296

open Filter

/-- The reciprocal sum of a finite set of natural numbers, as a rational number. -/
def recipSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / n

/-- There are `k` pairwise disjoint subsets of `{1, ..., N}` with reciprocal sum `1`. -/
def HasDisjointUnitDecomps (N k : ℕ) : Prop :=
  ∃ f : Fin k → Finset ℕ,
    (∀ i, f i ⊆ Finset.Icc 1 N) ∧
    (∀ i, recipSum (f i) = 1) ∧
    (∀ i j : Fin k, i ≠ j → Disjoint (f i) (f j))

/--
Let $N\geq 1$ and let $k(N)$ be maximal such that there are $k$ disjoint $A_1,\ldots,A_k\subseteq \{1,\ldots,N\}$ with $\sum_{n\in A_i}\frac{1}{n}=1$ for all $i$. Estimate $k(N)$. Is it true that $k(N)=o(\log N)$?

Hunter and Sawhney observed that Bloom's theorem [Bl21], together with the greedy
argument, gives $k(N)=(1-o(1))\log N$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos296.lean"]
theorem erdos_296 :
    (∀ N k : ℕ, HasDisjointUnitDecomps N k → (k : ℚ) ≤ recipSum (Finset.Icc 1 N)) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ N : ℕ in atTop,
        HasDisjointUnitDecomps N ⌊(1 - ε) * Real.log N⌋₊) := by
  sorry

end Erdos296
