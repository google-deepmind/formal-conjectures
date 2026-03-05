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
# Erdős Problem 356

Is there some $c > 0$ such that, for all sufficiently large $n$, there exist integers
$a_1 < \cdots < a_k \leq n$ with at least $cn^2$ distinct contiguous subsequence sums?

*Reference:* [erdosproblems.com/356](https://www.erdosproblems.com/356)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[Be23b] Beker, A., _On distinct consecutive differences_. (2023).
-/

open Finset BigOperators

namespace Erdos356

/-- The set of all contiguous subsequence sums of a finite integer sequence.
For a sequence $a : \operatorname{Fin} k \to \mathbb{Z}$, this is
$\{\sum_{i=u}^{v} a_i : 0 \leq u \leq v < k\}$. -/
def contiguousSubSums {k : ℕ} (a : Fin k → ℤ) : Finset ℤ :=
  ((univ ×ˢ univ).filter (fun p : Fin k × Fin k => p.1 ≤ p.2)).image
    (fun p => ∑ i ∈ Icc p.1 p.2, a i)

/--
Erdős Problem 356 [ErGr80, p.58]:

Is there some $c > 0$ such that, for all sufficiently large $n$, there exist
integers $a_1 < \cdots < a_k \leq n$ such that there are at least $cn^2$ distinct integers
of the form $\sum_{u \leq i \leq v} a_i$ (contiguous subsequence sums)?

Solved in the affirmative by Beker [Be23b].
-/
@[category research solved, AMS 5 11]
theorem erdos_356 :
    answer(True) ↔
    ∃ c : ℝ, c > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ (k : ℕ) (a : Fin k → ℤ),
      StrictMono a ∧
      (∀ i : Fin k, a i ≤ ↑n) ∧
      (↑(contiguousSubSums a).card : ℝ) ≥ c * (↑n : ℝ) ^ 2 := by
  sorry

end Erdos356
