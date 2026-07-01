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
# Erdős Problem 333

*References:*
- [erdosproblems.com/333](https://www.erdosproblems.com/333)
- [ErNe77] Erdős, P. and Newman, D. J., *Bases for sets of integers*. J. Number Theory (1977),
  420-425.
-/

open Classical Filter Asymptotics

open scoped Pointwise

namespace Erdos333

/--
Let $A\subseteq \mathbb{N}$ be a set of density zero. Does there exist a $B$ such that
$A\subseteq B+B$ and
\[\lvert B\cap \{1,\ldots,N\}\rvert =o(N^{1/2})\]
for all large $N$?

The answer is no. Erdős and Newman [ErNe77] have proved this is true when $A$ is the set of
squares. In fact, Theorem 2 of [ErNe77] already implies a negative answer to this problem, but
this seems to have been overlooked by Erdős and Graham.

See also [806].
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos333.lean"]
theorem erdos_333 : answer(False) ↔
    ∀ A : Set ℕ, A.HasDensity 0 →
      ∃ B : Set ℕ, A ⊆ B + B ∧
        (fun N => (((Finset.Icc 1 N).filter (· ∈ B)).card : ℝ)) =o[atTop]
          fun N => Real.sqrt N := by
  sorry

end Erdos333
