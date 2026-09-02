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
# Erdős Problem 467

*Reference:* [erdosproblems.com/467](https://www.erdosproblems.com/467)
-/

namespace Erdos467

open Filter

/-- The finite set of primes at most $x$. -/
def primesUpTo (x : ℕ) : Finset ℕ :=
  (Finset.Icc 2 x).filter Nat.Prime

/-- The sets $A$ and $B$ form a disjoint nonempty decomposition of the primes up to $x$. -/
def PrimePartitionUpTo (x : ℕ) (A B : Finset ℕ) : Prop :=
  A.Nonempty ∧
    B.Nonempty ∧
      A ∪ B = primesUpTo x ∧
        A ∩ B = ∅

/--
The selected congruence classes cover every $n<x$ from both sides of the partition.
-/
def CongruenceCover (x : ℕ) (residue : ℕ → ℕ) (A B : Finset ℕ) : Prop :=
  ∀ n : ℕ,
    n < x →
      (∃ p : ℕ, p ∈ A ∧ n % p = residue p % p) ∧
        ∃ q : ℕ, q ∈ B ∧ n % q = residue q % q

/--
For every sufficiently large $x$, choose a congruence class $a_p\pmod p$ for each prime $p\leq x$.
Can the primes be decomposed into two nonempty sets $A$ and $B$ such that every $n<x$ lies in a
chosen class from $A$ and in a chosen class from $B$?

This follows the interpretation on the Erdős Problems website, which notes that the original
source omits some crucial quantifiers.
-/
@[category research open, AMS 11]
theorem erdos_467 : answer(sorry) ↔
    ∀ᶠ x in atTop, ∃ residue : ℕ → ℕ, ∃ A B : Finset ℕ,
      PrimePartitionUpTo x A B ∧ CongruenceCover x residue A B := by
  sorry

end Erdos467
