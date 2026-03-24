/-
Copyright 2025 The Formal Conjectures Authors.
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
# Erdős Problem 287

*Reference:* [erdosproblems.com/287](https://www.erdosproblems.com/287)
-/

namespace Erdos287

def max_gap (k : ℕ) (s : Fin k → ℕ ) : ℕ  :=
   Finset.sup Finset.univ (fun i : Fin (k - 1) =>
      s  ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/-
Let $k\geq2$. Is it true that, for any distinct integers
$1 < n_1 < \cdots < n_k$ such that $\sum_{i=1}^k \frac{1}{n_i} = 1$,
we must have $\max(n_{i+1} - n_i) \geq 3$?
-/
@[category research open, AMS 11]
theorem erdos_287 (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ) (smono : StrictMono s) (s1 : 1 < s ⟨0, by omega⟩) :
    answer(sorry) ↔ ∑ i : Fin k, 1/ (s i : ℕ) = 1 →
    3 ≤ max_gap k s:= by
  sorry

end Erdos287
