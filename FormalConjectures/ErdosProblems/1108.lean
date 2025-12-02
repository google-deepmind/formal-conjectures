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
# Erdős Problem 1108

*Reference:* [erdosproblems.com/1108](https://www.erdosproblems.com/1108)

We look at sums of factorials over finite sets of natural numbers
and ask how often these sums can be perfect powers, or more generally
"powerful" numbers.

Let
\[
  A = \Bigl\{ \sum_{n \in S} n! : S \subset \mathbb{N} \text{ finite} \Bigr\}.
\]

The problem asks:

1. Fix an integer `k ≥ 2`. Does `A` contain only finitely many perfect `k`-th
   powers?
2. Does `A` contain only finitely many powerful numbers (i.e. numbers in which
   every prime divisor appears with exponent at least `2`)?
-/

open Nat

/-- The set `FactorialSums` is the set `A` of all finite sums of factorials
\{ ∑\_{n∈S} n! : S ⊂ ℕ finite \}. -/
abbrev Nat.FactorialSums : Set ℕ :=
  {m | ∃ S : Finset ℕ, m = S.sum (fun n => Nat.factorial n)}

/-- A natural number `n` is a perfect `k`-th power if there is some `m`
with `n = m^k`. We will only be interested in the case `2 ≤ k`. -/
def Nat.IsKthPower (k n : ℕ) : Prop :=
  ∃ m : ℕ, n = m ^ k

/-- A powerful number is a positive integer `n` such that whenever a prime
`p` divides `n`, we also have `p^2 ∣ n`. -/
def Nat.IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- The subset of `FactorialSums` consisting of perfect `k`-th powers. -/
abbrev Nat.FactorialSumsKthPowers (k : ℕ) : Set ℕ :=
  {n | n ∈ Nat.FactorialSums ∧ Nat.IsKthPower k n}

/-- The subset of `FactorialSums` consisting of powerful numbers. -/
abbrev Nat.FactorialSumsPowerful : Set ℕ :=
  {n | n ∈ Nat.FactorialSums ∧ Nat.IsPowerful n}

namespace Erdos1108

/-- First part of Erdős Problem 1108.

Let
`A = Nat.FactorialSums = { ∑ n∈S, n! : S ⊂ ℕ finite }`.

For each integer `k ≥ 2`, does `A` contain only finitely many perfect `k`-th
powers?

Formally: is it true that for every `k ≥ 2`, the set of `k`-th powers in `A`
is finite? -/
@[category research open, AMS 11]
theorem erdos_1108.parts.i :
    (∀ k, 2 ≤ k → (Nat.FactorialSumsKthPowers k).Finite) ↔
      answer (sorry) := by
  sorry

/-- Second part of Erdős Problem 1108.

Does the set `A = Nat.FactorialSums` contain only finitely many powerful
numbers?

Formally: is the set of powerful elements of `Nat.FactorialSums` finite? -/
@[category research open, AMS 11]
theorem erdos_1108.parts.ii :
    (Nat.FactorialSumsPowerful).Finite ↔
      answer (sorry) := by
  sorry

/-- A small sanity check: the empty sum is allowed, so `0` lies in
`Nat.FactorialSums`. We record this as a test lemma. -/
@[category test, AMS 11]
theorem erdos_1108.variants.zero_mem_FactorialSums :
    0 ∈ Nat.FactorialSums := by
  refine ⟨∅, by simp⟩

/-- Another basic example: the singletons `{n}` give `n! ∈ Nat.FactorialSums`. -/
@[category test, AMS 11]
theorem erdos_1108.variants.factorial_mem_FactorialSums (n : ℕ) :
    Nat.factorial n ∈ Nat.FactorialSums := by
  refine ⟨{n}, by simp⟩

end Erdos1108
