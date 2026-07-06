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
# Erdős Problem 105

*References:*
- [erdosproblems.com/105](https://www.erdosproblems.com/105)
- [ErPu95] Erdős, P. and Purdy, G., Two combinatorial problems in the plane. Discrete Comput.
  Geom. (1995), 441-443.
-/

open EuclideanGeometry

namespace Erdos105

/--
Let $A,B\subset \mathbb{R}^2$ be disjoint sets of size $n$ and $n-3$ respectively,
with not all of $A$ contained on a single line. Is there a line which contains at
least two points from $A$ and no points from $B$?

This has been disproved by an explicit counterexample.
-/
@[category research solved, AMS 51,
formal_proof using lean4 at
"https://github.com/plby/lean-proofs/blob/main/src/v4.30.0/ErdosProblems/Erdos105.lean#L287"]
theorem erdos_105 : answer(False) ↔
    ∀ (A B : Finset ℝ²) (n : ℕ),
      Disjoint A B →
      A.card = n →
      B.card = n - 3 →
      ¬ Collinear ℝ (A : Set ℝ²) →
      ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ ∀ b ∈ B, b ∉ affineSpan ℝ {p, q} := by
  sorry

end Erdos105
