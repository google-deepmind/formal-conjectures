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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 157

*References:*
- [erdosproblems.com/157](https://www.erdosproblems.com/157)
- [ESS94] Erdős, P. and Sárközy, A. and Sós, T., *On sum sets of Sidon sets, I*. Journal of Number
  Theory (1994), 329-347.
- [Er94b] Erdős, Paul, *Some problems in number theory, combinatorics and combinatorial geometry*.
  Math. Pannon. (1994), 261-269.
- [Pi23] Pilatte, C., *A solution to the Erdős–Sárközy–Sós problem on asymptotic Sidon bases of
  order 3*. Compositio Math. (2024), 1418-1432.
-/

@[expose] public section

namespace Erdos157

/--
Does there exist an infinite Sidon set which is an asymptotic basis of order $3$?

Yes, as shown by Pilatte [Pi23].
-/
@[category research solved, AMS 5 11]
theorem erdos_157 : answer(True) ↔
    ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ A.IsAsymptoticAddBasisOfOrder 3 := by
  sorry

end Erdos157
