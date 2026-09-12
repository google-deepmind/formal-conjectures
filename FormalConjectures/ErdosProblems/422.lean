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

import FormalConjecturesUtil

/-!
# Erdős Problem 422

*References:*
- [erdosproblems.com/422](https://www.erdosproblems.com/422)
- [OEIS A005185](https://oeis.org/A005185)
-/

namespace Erdos422

open Filter
open scoped Topology

/--
`IsHofstadterQ f` means that $f$ is Hofstadter's $Q$-sequence (OEIS A005185): $f(1) = f(2) = 1$
and for $n > 2$
$$
f(n) = f(n - f(n - 1)) + f(n - f(n - 2)),
$$
where the recurrence requires $f(n - 1) < n$ and $f(n - 2) < n$, so that both arguments on the
right-hand side are positive integers. The sequence begins $1, 1, 2, 3, 3, 4, \ldots$.

At most one function satisfies this predicate. Some function satisfies it if and only if $f(n)$ is
well-defined for all $n$, which is not known.
-/
def IsHofstadterQ (f : ℕ+ → ℕ+) : Prop :=
  f 1 = 1 ∧ f 2 = 1 ∧
  ∀ n : ℕ+, 2 < n →
    f (n - 1) < n ∧ f (n - 2) < n ∧ f n = f (n - f (n - 1)) + f (n - f (n - 2))

/-- The third term of Hofstadter's $Q$-sequence is $f(3) = f(2) + f(2) = 2$. -/
@[category test, AMS 11]
theorem erdos_422.test.f3 : ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → f 3 = 2 := by
  intro f ⟨h1, h2, h⟩
  obtain ⟨-, -, h3⟩ := h 3 (by decide)
  simp only [h3, show (3 : ℕ+) - 1 = 2 from rfl, show (3 : ℕ+) - 2 = 1 from rfl, h1, h2]
  rfl

/-- The fourth term of Hofstadter's $Q$-sequence is $f(4) = f(2) + f(3) = 3$. -/
@[category test, AMS 11]
theorem erdos_422.test.f4 : ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → f 4 = 3 := by
  intro f hf
  have h3 := erdos_422.test.f3 f hf
  obtain ⟨h1, h2, h⟩ := hf
  obtain ⟨-, -, h4⟩ := h 4 (by decide)
  simp only [h4, show (4 : ℕ+) - 1 = 3 from rfl, show (4 : ℕ+) - 2 = 2 from rfl, h2, h3]
  rfl

/--
Let $f(1) = f(2) = 1$ and for $n > 2$
$$
f(n) = f(n - f(n - 1)) + f(n - f(n - 2)).
$$
Does $f(n)$ miss infinitely many integers?
-/
@[category research open, AMS 11]
theorem erdos_422 : answer(sorry) ↔
    ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → Set.Infinite {n | ∀ x, f x ≠ n} := by
  sorry

/--
Is $f$ surjective?
-/
@[category research open, AMS 11]
theorem erdos_422.variants.surjective : answer(sorry) ↔
    ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → f.Surjective := by
  sorry

/--
How does $f$ grow?
-/
@[category research open, AMS 11]
theorem erdos_422.variants.growth_rate :
    ∀ f : ℕ+ → ℕ+, IsHofstadterQ f →
    (fun n ↦ (f n : ℝ)) =O[atTop] (answer(sorry) : ℕ+ → ℝ) := by
  sorry

/--
Does $f$ become stationary at some point?
-/
@[category research open, AMS 11]
theorem erdos_422.variants.eventually_const : answer(sorry) ↔
    ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → EventuallyConst f atTop := by
  sorry

end Erdos422
