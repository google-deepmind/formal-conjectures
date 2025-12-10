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
# Erdős Problem 881

Let `A ⊂ ℕ` be an additive basis of order `k` which is *minimal*, in the sense that
if `B ⊂ A` is any infinite subset, then `A \ B` is not a basis of order `k`.

> Must there exist an infinite `B ⊂ A` such that `A \ B` is a basis of order `k + 1`?

We interpret "additive basis of order `k`" as an asymptotic additive basis of order `k`,
using the predicate `Set.IsAsymptoticAddBasisOfOrder` from additive combinatorics.

*Reference:* [erdosproblems.com/881](https://www.erdosproblems.com/881)
-/

open Set

namespace Erdos881

/--
A *minimal* additive basis of order `k` is a set `A` such that
* `A` is an asymptotic additive basis of order `k`, and
* for every infinite subset `B ⊆ A`, the complement `A \ B` is *not*
  an asymptotic additive basis of order `k`.
-/
def IsMinimalAsymptoticAddBasisOfOrder (k : ℕ) (A : Set ℕ) : Prop :=
  A.IsAsymptoticAddBasisOfOrder k ∧
    ∀ ⦃B : Set ℕ⦄, B ⊆ A → B.Infinite → ¬ (A \ B).IsAsymptoticAddBasisOfOrder k

/--
**Erdős Problem 881.**

Let `A ⊂ ℕ` be an additive basis of order `k` which is minimal in the sense that
if `B ⊂ A` is any infinite set, then `A \ B` is not a basis of order `k`.

Must there exist an infinite `B ⊂ A` such that `A \ B`
is an additive basis of order `k + 1`?
-/
@[category research open, AMS 5 11]
theorem erdos_881 :
    (∀ (k : ℕ) (A : Set ℕ),
      IsMinimalAsymptoticAddBasisOfOrder k A →
        ∃ (B : Set ℕ), B ⊆ A ∧ B.Infinite ∧
          (A \ B).IsAsymptoticAddBasisOfOrder (k + 1)) ↔
      answer(sorry) := by
  sorry

end Erdos881

