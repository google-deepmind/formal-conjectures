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
# Erdos Problem 342

*References:*
- [erdosproblems.com/342](https://www.erdosproblems.com/342)
- [OEIS A002858](https://oeis.org/A002858)
-/

namespace Ulam

/--
`UniqueUlamSum u n m` means that `m` has a unique representation as `u i + u j`
with `1 ≤ i < j ≤ n`.
-/
def UniqueUlamSum (u : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃! ij : ℕ × ℕ,
    1 ≤ ij.1 ∧ ij.1 < ij.2 ∧ ij.2 ≤ n ∧
    m = u ij.1 + u ij.2

/--
`IsUlamSequence u` means that the sequence `u` satisfies the recurrence for Ulam's sequence:
`u 1 = 1`, `u 2 = 2`, and for `n ≥ 2`, `u (n+1)` is the least integer greater than `u n`
that has a unique representation as `u i + u j` with `1 ≤ i < j ≤ n`.
-/
def IsUlamSequence (u : ℕ → ℕ) : Prop :=
  u 1 = 1 ∧
  u 2 = 2 ∧
  ∀ n : ℕ, 2 ≤ n →
    u (n + 1) > u n ∧
    UniqueUlamSum u n (u (n + 1)) ∧
    ∀ m : ℕ, u n < m → UniqueUlamSum u n m → u (n + 1) ≤ m

/--
**Ulam pair conjecture**
There are infinitely many pairs of consecutive Ulam numbers differing by `2`.
-/
@[category research open, AMS 11]
theorem ulam_infinitely_many_pairs :
    answer(sorry) ↔
      ∀ u : ℕ → ℕ, IsUlamSequence u →
        ∀ N : ℕ, ∃ n ≥ N, u (n + 1) = u n + 2 := by
  sorry

end Ulam
