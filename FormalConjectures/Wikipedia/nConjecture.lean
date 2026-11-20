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

module

public import FormalConjecturesUtil
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.RingTheory.Radical.NatInt            -- for radical
import Mathlib.Analysis.SpecialFunctions.Pow.Real   -- for real numbers and powers of real numbers


/-!
# $n$-Conjecture
We state the first formulation of the $n$-Conjecture.
If $n ≥ 3$ and $a₁, ..., aₙ$ are integers such that
  (i) $GCD(a₁, ..., aₙ) = 1,$
  (ii) $a₁ + ... + aₙ = 0,$ and
  (iii) no proper subsum of $a₁, ..., aₙ$ equals $0$,
then for every $ε > 0,$ there is a constant $C$ depending on $ε$ and $n$ such that
    $max(|a₁|, ..., |aₙ|) < C · rad(|a₁| ⋯ |aₙ|)^{2n - 5 + ε}.$

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/N_conjecture)
-/

@[expose] public section


open UniqueFactorizationMonoid                      -- for radical
open Real


namespace nConjecture


/--
The $n$-Conjecture is a statement about an integer $n$ greater than or equal to 3
and a sequence of integers $a₁, ..., aₙ$ with the properties that
  (i) $GCD(a₁, ..., aₙ) = 1,$
  (ii) $a₁ + ... + aₙ = 0,$ and
  (iii) no proper subsum of $a₁, ..., aₙ$ equals $0$.
-/
structure nConjectureInput where
  n : ℕ
  a : ℕ → ℤ   -- this represents the elements a₁, ..., aₙ. Should change domain at some point
  hn : n ≥ 3
  h₁ : (Finset.Icc 1 n).gcd a = 1
  h₂ : ∑ i ∈ Finset.Icc 1 n, a i = 0
  h₃ : ∀ X ∈ (Finset.Icc 1 n).powerset, X ≠ (Finset.Icc 1 n) ∧ X ≠ ∅ → ∑ i ∈ X, a i ≠ 0
  -- maybe find better way for proper power set

/--
This is the indexing set of the sequence of integers in the input for the n-Conjecture.
-/
def nConjectureInput.interval (A : nConjectureInput) : (Finset ℕ) := Finset.Icc 1 A.n

/--
This is the maximum absolute value of an integer in the sequence.
-/
def nConjectureInput.max (A : nConjectureInput) : ℕ :=
  (A.interval).sup (fun i => (A.a i).natAbs)

/--
This is the radical of the product of the elements in the sequence of integers.
-/
noncomputable def nConjectureInput.rad (A : nConjectureInput) : ℕ :=
  radical (∏ i ∈ A.interval, (A.a i).natAbs)
/--
The $n$-Conjecture: for every $ε > 0,$ there is a constant $C$ depending on $ε$ and $n$ such that
    $max(|a₁|, ..., |aₙ|) < C · rad(|a₁| ⋯ |aₙ|)^{2n - 5 + ε}.$
-/
@[category research open]
theorem nConjecture : ∀ ε : ℝ, ε > 0 → ∀ m : ℕ, ∃ C : ℝ, ∀ (A : nConjectureInput),
  A.n = m → A.max < C * A.rad ^ (2 * A.n - 5 + ε) := by                 -- maybe change A.n = m
  sorry

end nConjecture
