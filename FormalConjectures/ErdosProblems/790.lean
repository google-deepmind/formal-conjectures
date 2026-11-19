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

/-!
# Erdős Problem 790

*References:*
- [erdosproblems.com/790](https://www.erdosproblems.com/790)
-/

@[expose] public section

open Filter

namespace Erdos790


def GenSumFree (X : Finset ℤ) : Prop :=
  ∀ ( r : ℕ ), ∀ (a : Fin (r+2) → ℤ), (∀ i : Fin (r + 2),  a i ∈ X)
  → Function.Injective a → (∑ i ∈ Finset.univ \ {0}, a i ≠ a 0)

def LowerBound ( n m : ℕ ) : Prop :=
  ∀ (A : Finset ℤ), A.card = n →
    ∃ (B : Finset ℤ), B ⊆ A ∧ B.card ≥ m ∧ GenSumFree B

def MaxLowerBound (l : ℕ → ℕ) : Prop :=
   ∀ (n : ℕ), LowerBound n (l n) ∧ (∀ ( m : ℕ ), LowerBound n m → (l n ≥ m) )

/--
Let l ( n ) be maximal such that if A ⊂ Z with | A | = n then there exists a sum-free B ⊆ A with | B | ≥ l ( n ) - that is, B is such that there are no solutions to
a 1 = a 2 + ⋯ + a r
with a i ∈ B all distinct.

Is it true that `lim_{n → ∞} l(n) * n^{-1/2} = ∞`?
-/
@[category research open, question, AMS 5]
theorem Erdos_790_Question1 (l : ℕ → ℕ) (hl : MaxLowerBound l) :=
  Tendsto (fun n : ℕ => (l n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop atTop := by
    sorry

/--
Let l ( n ) be maximal such that if A ⊂ Z with | A | = n then there exists a sum-free B ⊆ A with | B | ≥ l ( n ) - that is, B is such that there are no solutions to
a 1 = a 2 + ⋯ + a r
with a i ∈ B all distinct.

Is it true that there exists `c > 0` such that for sufficiently large `n` we have `l(n) < n^(1-c)`?
-/
@[category research open, question, AMS 5]
theorem Erdos_790_Question2 (l : ℕ → ℕ) (hl : MaxLowerBound l) :=
  ∃ (c : ℝ), c > 0 ∧ ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
    (l n : ℝ) < (n : ℝ) ^ (1 - c) := by
      sorry




end Erdos790
