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
# Erdős Problem 1094

*Reference:* [erdosproblems.com/1094](https://www.erdosproblems.com/1094)

For integers `n, k` with `n ≥ 2k`, consider the binomial coefficient `Nat.choose n k`.
Erdős conjectured that, apart from finitely many exceptions, the least prime factor
of `Nat.choose n k` is at most `max (n / k) k`.
-/

open scoped Nat
open Nat

/-- The least prime factor of the binomial coefficient `Nat.choose n k`,
defined using `Nat.minFac`. For the range `n ≥ 2k ≥ 4` that appears in the problem,
this really is the least prime divisor of `Nat.choose n k`. -/
abbrev Nat.binomMinFac (n k : ℕ) : ℕ :=
  Nat.minFac (Nat.choose n k)

/-- The predicate saying that the conjectured upper bound on the least
prime factor of `Nat.choose n k` holds for the given pair `(n, k)`.

We only look at the range `n ≥ 2k` and `k ≥ 2`, as in the problem statement. -/
def Nat.BinomialPrimeBound (n k : ℕ) : Prop :=
  2 ≤ k ∧ 2 * k ≤ n ∧ binomMinFac n k ≤ max (n / k) k

/-- The set of "bad" pairs `(n, k)` in the range `n ≥ 2k`, `k ≥ 2` for which
the least prime factor of `Nat.choose n k` is *larger* than `max (n / k) k`.
The conjecture is that this set is finite. -/
def Nat.BadBinomialPairs : Set (ℕ × ℕ) :=
  { nk |
    let n := nk.1
    let k := nk.2
    2 ≤ k ∧ 2 * k ≤ n ∧ max (n / k) k < binomMinFac n k }

namespace Erdos1094

/-- Erdős Problem 1094.

For all `n, k` with `n ≥ 2k` and `k ≥ 2`, the least prime factor of the binomial
coefficient `Nat.choose n k` is at most `max (n / k) k`, with only finitely many
exceptions.

Equivalently, the set of "bad" pairs `(n, k)` failing this bound is finite. -/
@[category research open, AMS 11]
theorem erdos_1094.main :
    (Nat.BadBinomialPairs).Finite ↔ answer (sorry) := by
  sorry

/-- A small sanity check: for any fixed `k ≥ 2`, the condition
`Nat.BinomialPrimeBound n k` only constrains `n` once we are in the range `n ≥ 2k`. -/
@[category test, AMS 11]
theorem erdos_1094.variants.bound_requires_range {n k : ℕ}
    (h : Nat.BinomialPrimeBound n k) :
    2 ≤ k ∧ 2 * k ≤ n := by
  exact ⟨h.1, h.2.1⟩

end Erdos1094
