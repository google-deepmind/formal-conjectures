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
# Erdős Problem 484

*References:*
- [erdosproblems.com/484](https://www.erdosproblems.com/484)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Er80] Erdős, Paul, *A survey of problems in combinatorial number theory*. Ann. Discrete Math.
  (1980), 89-115.
- [ESS89] Erdős, P., Sárközy, A., and Sós, V. T., *On a conjecture of Roth and some related
  problems. I*. (1989), 47-59.
-/

namespace Erdos484

open scoped Classical in
/--
Prove that there exists an absolute constant $c>0$ such that, whenever $\{1,\ldots,N\}$ is
$k$-coloured (and $N$ is large enough depending on $k$) then there are at least $cN$ many
integers in $\{1,\ldots,N\}$ which are representable as a monochromatic sum (that is, $a+b$
where $a,b\in \{1,\ldots,N\}$ are in the same colour class and $a\neq b$).

A conjecture of Roth. Solved by Erdős, Sárközy, and Sós [ESS89], who in fact prove that
there are at least $\frac{N}{2}-O(N^{1-1/2^{k+1}})$ many even numbers which are of this form.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos484.lean"]
theorem erdos_484 :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : ℕ → Fin k,
      c * N ≤ (((Finset.Icc 1 N).filter fun n =>
        ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N,
          a ≠ b ∧ f a = f b ∧ a + b = n).card : ℝ) := by
  sorry

end Erdos484
