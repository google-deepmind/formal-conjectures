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
# Erdős Problem 734

*References:*
- [erdosproblems.com/734](https://www.erdosproblems.com/734)
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved.
  Combinatorica (1981), 25-42.
- [dBEr48] de Bruijn, N. G. and Erdős, P., On a combinatorial problem. Nederl. Akad. Wetensch.,
  Proc. (1948), 1277--1279 = Indagationes Math. 10, 421--423.
-/

namespace Erdos734

open Filter Asymptotics

/--
Find, for all large $n$, a non-trivial pairwise balanced block design $A_1,\ldots,A_m\subseteq
\{1,\ldots,n\}$ such that, for all $t$, there are $O(n^{1/2})$ many $i$ such that $\lvert
A_i\rvert=t$.
-/
@[category research open, AMS 5]
theorem erdos_734 :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∃ H : Finset (Finset (Fin n)), H.IsPairwiseBalancedDesign ∧
      (∀ e ∈ H, e.card < n) ∧ ∀ t : ℕ,
        ({e ∈ H | e.card = t}.card : ℝ) ≤ C * Real.sqrt n := by
  sorry

end Erdos734
