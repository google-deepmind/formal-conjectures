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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 422

*References:*
- [erdosproblems.com/422](https://www.erdosproblems.com/422)
- [OEIS A005185](https://oeis.org/A005185)
-/

@[expose] public section

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
@[category research open, question, AMS 11]
theorem erdos_422 :
    ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → Set.Infinite {n | ∀ x, f x ≠ n} := by
  sorry

/--
Is $f$ surjective?
-/
@[category research open, question, AMS 11]
theorem erdos_422.variants.surjective :
    ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → f.Surjective := by
  sorry

def erdos_422.variants.growth_rate.answer : ℕ+ → ℝ := sorry

/--
How does $f$ grow?
-/
@[category research open, question value, AMS 11]
theorem erdos_422.variants.growth_rate :
    ∀ f : ℕ+ → ℕ+, IsHofstadterQ f →
    (fun n ↦ (f n : ℝ)) =O[atTop] erdos_422.variants.growth_rate.answer := by
  sorry

/--
Hofstadter's $Q$-sequence is not eventually constant: if $f(n) = c$ for all large $n$, then the
recurrence gives $c = f(n - c) + f(n - c) = 2c$.
-/
@[category API, AMS 11]
theorem IsHofstadterQ.not_eventuallyConst {f : ℕ+ → ℕ+} (hf : IsHofstadterQ f) :
    ¬ EventuallyConst f atTop := by
  obtain ⟨-, -, hf⟩ := hf
  intro h
  obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.mp h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  have hc0 := c.pos
  -- Subtracting `k ≤ c + 1` from `n = N + c + 2` leaves an index that is still at least `N`.
  have key (k : ℕ+) (hk : (k : ℕ) ≤ c + 1) : f (N + c + 2 - k) = c := hN _ <| by
    have hlt : k < N + c + 2 := by
      rw [← PNat.coe_lt_coe]; push_cast; omega
    rw [← PNat.coe_le_coe, PNat.sub_coe, if_pos hlt]
    push_cast; omega
  have hn : f (N + c + 2) = c := hN _ <| by
    rw [← PNat.coe_le_coe]; push_cast; omega
  obtain ⟨-, -, hrec⟩ := hf (N + c + 2) (PNat.lt_add_left 2 (N + c))
  -- The recurrence at `n` now reads `c = c + c`.
  rw [hn, key 1 (Nat.le_add_left 1 c), key 2 (by push_cast; omega), key c (by omega)] at hrec
  exact (PNat.lt_add_right c c).ne hrec

/--
Does $f$ become stationary at some point?

No: see `IsHofstadterQ.not_eventuallyConst`. The statement is existential, so the answer does
not depend on whether $f(n)$ is well-defined for all $n$.
-/
@[category textbook, AMS 11]
theorem erdos_422.variants.eventually_const : answer(False) ↔
    ∃ f : ℕ+ → ℕ+, IsHofstadterQ f ∧ EventuallyConst f atTop :=
  ⟨False.elim, fun ⟨_, hf, h⟩ ↦ hf.not_eventuallyConst h⟩

/--
Is $f(n)$ well-defined for all $n$?
-/
@[category research open, AMS 11]
theorem erdos_422.variants.well_defined : answer(sorry) ↔ ∃ f : ℕ+ → ℕ+, IsHofstadterQ f := by
@[category research open, question, AMS 11]
theorem erdos_422.variants.eventually_const :
    ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → EventuallyConst f atTop := by
  sorry

end Erdos422
