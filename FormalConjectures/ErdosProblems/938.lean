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
# Erdős Problem 938

*Reference:* [erdosproblems.com/938](https://www.erdosproblems.com/938)
-/
open Nat

/--
Let $A=\{n_1 < n_2 < \cdots\}$ be the sequence of powerful numbers (if $p\mid n$ then $p^2\mid n$).
Are there only finitely many three-term progressions of consecutive terms $n_k,n_{k+1},n_{k+2}$?
-/
@[category research open, AMS 11]
theorem erdos_938 : {P : Finset ℕ | Set.IsAPOfLength P.toSet 3 ∧ ∃ k,
    P = {nth Powerful k, nth Powerful (k + 1), nth Powerful (k + 2)}}.Finite ↔ answer(sorry) := by
  sorry
