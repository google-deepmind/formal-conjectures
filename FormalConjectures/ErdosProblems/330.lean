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
# Erdős Problem 330

*Reference:* [erdosproblems.com/330](https://www.erdosproblems.com/330)
-/

namespace Erdos330

open Set
open scoped BigOperators Pointwise

/-- `Rep A m h` means `m` is a sum of exactly `h` elements of `A`, which is `m ∈ h • A`.

Exactly `h` rather than at most `h`, for two reasons. It is the notion Erdős states the problem
with, via `f_2(m)`, the number of solutions of `m = a_i + a_j` [Er80]. And it is the notion
`IsAsymptoticAddBasisOfOrder` uses below, so the statement is not switching between two meanings
of "representable" partway through.

Allowing fewer than `h` summands also breaks the statement outright: taking one summand makes
every element of `A` count as represented, so `UnrepWithout A n h` would contain no element of
`A` besides possibly `n`. Those are exactly the integers the problem is about. If `a ∈ A` with
`a ≠ n` is only expressible as `a = n + b`, it cannot be represented without `n` and belongs in
the set, but the one-element sum `a` itself would have excluded it. -/
def Rep (A : Set ℕ) (m h : ℕ) : Prop := m ∈ h • A

/-- Integers **not** representable as a sum of exactly `h` elements of `A`
**while avoiding** `n`. -/
def UnrepWithout (A : Set ℕ) (n h : ℕ) : Set ℕ :=
  {m | ¬ Rep (A \ {n}) m h}

/-- An asymptotic additive basis of order `h` is minimal when one cannot obtain an asymptotic
additive basis by removing any element from it. -/
def MinAsymptoticAddBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  IsAsymptoticAddBasisOfOrder A h ∧ ∀ n ∈ A, ¬ IsAsymptoticAddBasisOfOrder (A \ {n}) h

/--
Does there exist a minimal basis $A \subset \mathbb{N}$ with positive density
such that, for any $n \in A$, the (upper) density of integers which
cannot be represented without using $n$ is positive?

Neither set is asked to have a density, only to have positive upper density, so
`Set.upperDensity` is used for both rather than `Set.HasPosDensity`. As with many of Erdős'
questions "positive density" here most likely means positive upper density, and in [Er80] he
considers either the lower or the upper density for the integers not representable without a
fixed `n`. Requiring the density to exist would ask a strictly harder question than the one
posed. See #3979.

Such a set exists, so the answer is yes. The linked proof gives one of order `2`.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/Jayyhk/erdos-lean/blob/a5ffc87b3d684fc00ea906b9e746c283740da900/problems/330/Erdos330.lean"]
theorem erdos_330_statement :
    answer(True) ↔ ∃ (A : Set ℕ), ∃ h, MinAsymptoticAddBasisOfOrder A h ∧
    0 < A.upperDensity ∧ ∀ n ∈ A, 0 < (UnrepWithout A n h).upperDensity := by
  sorry

end Erdos330
