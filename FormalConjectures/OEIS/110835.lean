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
# Smallest $m > 0$ such that there are no primes between $nm$ and $n(m+1)$ inclusive.

Sierpinski's conjecture (1958) is precisely that a(n) >= n for all n.

*References:*
- [A110835](https://oeis.org/A110835)
-/

namespace OeisA110835

open Nat Set

/--
The primary defining sequence `a`.
$a(n)$ is the smallest $m > 0$ such that there are no primes between $n \cdot m$
and $n \cdot (m+1)$ inclusive.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let IsPrimeFreeInterval (m : ℕ) : Prop :=
    ∀ p : ℕ, p.Prime → ¬ (n * m ≤ p ∧ p ≤ n * (m + 1))
  let s : Set ℕ := {m : ℕ | m > 0 ∧ IsPrimeFreeInterval m}
  sInf s

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 8 := by
  dsimp [a]
  have hleast : IsLeast {m : ℕ | m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (1 * m ≤ p ∧ p ≤ 1 * (m + 1))} 8 := by
    constructor
    · simp only [mem_setOf_eq, one_mul]
      refine ⟨by decide, ?_⟩
      intro p hp ⟨hge, hle⟩
      interval_cases p <;> revert hp <;> decide
    · rintro m ⟨hmpos, hfree⟩
      by_contra! hlt
      simp only [one_mul] at hfree
      interval_cases m
      · specialize hfree 2 (by decide); revert hfree; decide
      · specialize hfree 2 (by decide); revert hfree; decide
      · specialize hfree 3 (by decide); revert hfree; decide
      · specialize hfree 5 (by decide); revert hfree; decide
      · specialize hfree 5 (by decide); revert hfree; decide
      · specialize hfree 7 (by decide); revert hfree; decide
      · specialize hfree 7 (by decide); revert hfree; decide
  exact hleast.csInf_eq

@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by
  dsimp [a]
  have hleast : IsLeast {m : ℕ | m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (2 * m ≤ p ∧ p ≤ 2 * (m + 1))} 4 := by
    constructor
    · simp only [mem_setOf_eq]
      refine ⟨by decide, ?_⟩
      intro p hp ⟨hge, hle⟩
      interval_cases p <;> revert hp <;> decide
    · rintro m ⟨hmpos, hfree⟩
      by_contra! hlt
      interval_cases m
      · specialize hfree 2 (by decide); revert hfree; decide
      · specialize hfree 5 (by decide); revert hfree; decide
      · specialize hfree 7 (by decide); revert hfree; decide
  exact hleast.csInf_eq

@[category test, AMS 11]
theorem a_3 : a 3 = 8 := by
  dsimp [a]
  have hleast : IsLeast {m : ℕ | m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (3 * m ≤ p ∧ p ≤ 3 * (m + 1))} 8 := by
    constructor
    · simp only [mem_setOf_eq]
      refine ⟨by decide, ?_⟩
      intro p hp ⟨hge, hle⟩
      interval_cases p <;> revert hp <;> decide
    · rintro m ⟨hmpos, hfree⟩
      by_contra! hlt
      interval_cases m
      · specialize hfree 3 (by decide); revert hfree; decide
      · specialize hfree 7 (by decide); revert hfree; decide
      · specialize hfree 11 (by decide); revert hfree; decide
      · specialize hfree 13 (by decide); revert hfree; decide
      · specialize hfree 17 (by decide); revert hfree; decide
      · specialize hfree 19 (by decide); revert hfree; decide
      · specialize hfree 23 (by decide); revert hfree; decide
  exact hleast.csInf_eq

/--
Sierpinski's conjecture (1958) is precisely that $a(n) >= n$ for all $n$.
-/
@[category research open, AMS 11]
theorem conjecture : ∀ n > 0, a n ≥ n := by
  sorry

end OeisA110835
