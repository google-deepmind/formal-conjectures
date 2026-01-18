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
# Ben Green's Open Problem 37

What is the smallest subset of `ℕ` containing, for each `d = 1, …, N`,
an arithmetic progression of length `k` with common difference `d`?

*References:*
- [Ben Green's Open Problem 37](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.37)
- [Green & Tao, *The primes contain arbitrarily long arithmetic progressions* (arXiv:math/0404188)](https://arxiv.org/abs/math/0404188)
-/

namespace Green37

open Set Filter
open scoped Asymptotics

/-- `A` contains an arithmetic progression of length `k` and common difference `d` for every `d ∈ {1, …, N}`. -/
def IsAPCover (A : Set ℕ) (N k : ℕ) : Prop := ∀ d, 1 ≤ d ∧ d ≤ N → Set.ContainsAP A k d

/-- The minimum size of a subset of `ℕ` that contains, for each `d = 1, …, N`,
an arithmetic progression of length `k` with common difference `d`. -/
noncomputable def m (N k : ℕ) : ℕ :=
  sInf { m | ∃ A : Finset ℕ, A.card = m ∧ IsAPCover (A : Set ℕ) N k }

/--
Given a natural number `N`, what is the smallest size of a subset of `ℕ` that contains, for each `d = 1, …, N`,
an arithmetic progression of length `k` with common difference `d`.
-/
@[category research open, AMS 05 11]
theorem green_37 (N k : ℕ) :
    IsLeast { m | ∃ A : Finset ℕ, A.card = m ∧ IsAPCover (A : Set ℕ) N k } (answer(sorry)) := by
  sorry

/--
Asymptotic version: if `m(N, k)` is the size of the smallest such subset, then `m(N, k)` satisfies
some asymptotic condition as `N` grows.
-/
@[category research open, AMS 05 11]
theorem green_37_asymptotic (k : ℕ) :
    answer(sorry) ↔ ∃ f : ℕ → ℝ, (fun N ↦ (m N k : ℝ)) =O[atTop] f := by
  sorry

end Green37
