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
# Erdős Problem 872

*References:*
- [erdosproblems.com/872](https://www.erdosproblems.com/872)
- [erdosproblems.com/forum/thread/872](https://www.erdosproblems.com/forum/thread/872)
-/

namespace Erdos872

/-- A primitive subset of `{2, ..., n}` is a set in which no element divides another.
This matches the standard definition; `A ⊆ Finset.Icc 2 n` and for all distinct `a, b ∈ A`,
neither `a ∣ b` nor `b ∣ a`. -/
def IsPrimitive (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 n ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a ∣ b

/- The two-player primitive set game on `{2, ..., n}`.

A position is a pair `(A, R)` where `A ⊆ {2, ..., n}` is the currently-built primitive set
and `R ⊆ {2, ..., n} \ A` is the set of "remaining" elements that could still be added.

A legal move adds an element `x ∈ R` to `A` such that `A ∪ {x}` remains primitive, and removes
from `R` every multiple and every divisor of `x` (since those can never be added later).
The game ends when no legal move is possible, i.e., when `A` is a *maximal* primitive subset.

In the Maker-Breaker (length) game, the two players alternate moves but both make moves of the
same type (adding to `A`); one player ("Maker", or the Prolonger) aims to make the game last as
long as possible, and the other ("Breaker", or the Shortener) aims to end it as quickly as
possible. The *guaranteed length* `L(n)` is the minimum, over Shortener strategies, of the
maximum, over Prolonger strategies, of the number of moves played before the game terminates,
with both players moving optimally from the empty position.

This formalization fixes a single position type and a single move predicate, leaving the
alternating-strategy semantics to a separate `L` definition below. -/

/-- A position consists of the already-claimed primitive set and the still-available pool. -/
structure GamePos (n : ℕ) where
  claimed : Finset ℕ
  pool : Finset ℕ
  claimed_primitive : IsPrimitive n claimed
  pool_disjoint : Disjoint claimed pool
  pool_subset : pool ⊆ Finset.Icc 2 n
  pool_compatible : ∀ x ∈ pool, IsPrimitive n (insert x claimed)

/-- A legal move from position `p` picks an element `x` of the pool. The resulting position
has `x` added to the claimed set, and every multiple and divisor of `x` removed from the pool. -/
noncomputable def applyMove {n : ℕ} (p : GamePos n) (x : ℕ) (hx : x ∈ p.pool) :
    GamePos n := by
  refine
    { claimed := insert x p.claimed,
      pool := p.pool.filter (fun y => y ≠ x ∧ ¬ x ∣ y ∧ ¬ y ∣ x),
      claimed_primitive := ?_,
      pool_disjoint := ?_,
      pool_subset := ?_,
      pool_compatible := ?_ } <;> sorry

/-- The empty starting position on `{2, ..., n}`: nothing claimed, full pool available. -/
noncomputable def startPos (n : ℕ) : GamePos n where
  claimed := ∅
  pool := Finset.Icc 2 n
  claimed_primitive := ⟨by simp, by simp⟩
  pool_disjoint := by simp
  pool_subset := subset_refl _
  pool_compatible := by intro x hx; refine ⟨?_, ?_⟩ <;> simp_all

/-- The guaranteed length of the game starting from position `p`, with Prolonger moving first.
This is a Maker-Breaker game length: Prolonger maximizes, Shortener minimizes, players alternate. -/
noncomputable def gameLength {n : ℕ} : GamePos n → ℕ := sorry

/-- The Erdős-Cameron primitive-set game length on `{2, ..., n}`. -/
noncomputable abbrev L (n : ℕ) : ℕ := gameLength (startPos n)

/- ## Erdős Problem 872

The problem asks for asymptotic lower bounds on `L(n)`. Two specific targets are stated. -/

/-- Erdős Problem 872, weak form: for every `ε > 0`, the game length is at least `ε * n`
for all sufficiently large `n`. -/
@[category research open, AMS 5 11]
theorem erdos_872.parts.weak : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n in Filter.atTop, (L n : ℝ) ≥ ε * n := by
  sorry

/-- Erdős Problem 872, strong form: for every `ε > 0`, the game length is at least
`(1 - ε) * n / 2` for all sufficiently large `n`. -/
@[category research open, AMS 5 11]
theorem erdos_872.parts.strong : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n in Filter.atTop, (L n : ℝ) ≥ (1 - ε) * n / 2 := by
  sorry

/-- A trivial upper bound: every maximal primitive subset of `{2, ..., n}` has size at most
the number of elements of `{2, ..., n}` itself, so `L(n) ≤ n - 1`. -/
@[category research solved, AMS 5 11]
theorem erdos_872.trivial_upper_bound (n : ℕ) (hn : 2 ≤ n) :
    L n ≤ n - 1 := by sorry

/-- Forum-related variant (Angelo): the game length is at least `π(n)` (the prime counting
function), because the set of primes in `{2, ..., n}` is a maximal primitive subset and a
trivial Shortener-play upper-bounds the minimum maximal primitive subset size. -/
@[category research open, AMS 5 11]
theorem erdos_872.variants.prime_lower_bound : answer(sorry) ↔
    ∀ n ≥ 2, L n ≥ ((Finset.Icc 2 n).filter Nat.Prime).card := by
  sorry

/-- Buddhdev (2026) [erdosproblems.com/forum/thread/872]: candidate lower bound
`L(n) ≥ c_δ * n * (log log n)^2 / log n` for all sufficiently large `n`, for some `δ ∈ (0, 1/4)`
and `c_δ > 0`, conditional on the restricted safe-edge hypothesis on T2-strategy-generated
states (Proposition A.9, Definition 4.5). -/
@[category research open, AMS 5 11]
theorem erdos_872.variants.buddhdev_conditional : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop,
      (L n : ℝ) ≥ c * n * (Real.log (Real.log n))^2 / Real.log n := by
  sorry

end Erdos872
