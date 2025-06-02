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
# Erdős Problem 56

*Reference:* [erdosproblems.com/56](https://www.erdosproblems.com/56)
-/
/--
Say a set of natural numbers is `k`-weakly divisible if any `k+1` elements
of `A` are not relatively prime.
-/
def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
    ∀ s ∈ A.powersetCard (k+1), ¬ Pairwise Nat.Coprime

@[category API, AMS 11]
lemma weaklyDivisible_empty (k : ℕ): WeaklyDivisible k {} := by
  simp [WeaklyDivisible]

@[category API, AMS 11]
lemma weaklyDivisible_one (k : ℕ) : WeaklyDivisible k {1} := by
  simp [WeaklyDivisible, Pairwise]
  intro hk
  use 4, 2
  norm_num

--TODO(lezeau): we shouldn't need to open `Classical` here!
open Classical in
/--
`MaxWeaklyDivisible N k` is the size of the largest k-weakly divisible subset of `{1,..., N}`
-/
noncomputable def MaxWeaklyDivisible (N : ℕ) (k : ℕ) : ℕ :=
    (Finset.Icc 1 N).powerset.filter (WeaklyDivisible k) |>.sup
    Finset.card

@[category test, AMS 11]
example (k : ℕ) : MaxWeaklyDivisible 0 k = 0 := by
  simp [MaxWeaklyDivisible]

open Classical

@[category test, AMS 11]
example (k : ℕ) : MaxWeaklyDivisible 1 k = 1 := by
  simp [MaxWeaklyDivisible]
  have : (Finset.filter (WeaklyDivisible k) ({1} : Finset ℕ).powerset) = {{}, {1}} := by
    show Finset.filter (WeaklyDivisible k) {∅, {1}} = _
    rw [Finset.filter_insert (WeaklyDivisible k) ({} : Finset ℕ) {{1}}]
    simp only [weaklyDivisible_empty k, Finset.filter_singleton, weaklyDivisible_one]
    by_cases hk : k = 0 <;> simp [hk]
  rw [this]
  by_cases hk : k = 0 <;> simp [hk]

/--
`FirstPrimesMultiples N k` is the set of numbers in `{1,..., N}` that are
a multiple of one of the first `k` primes.
-/
noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
    (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)

@[category test, AMS 11]
example (k : ℕ) : (FirstPrimesMultiples 1 k).card = 0 := by
  simp [FirstPrimesMultiples, Finset.filter_singleton]
  intro n h
  by_contra hprime
  have : Nat.Prime 1 := by
    convert Nat.prime_nth_prime n
    exact hprime.symm
  tauto

/--
An example of a `k`-weakly divisible set is the subset of `{1, ..., N}`
containing the multiples of the first `k` primes.
-/
@[category API, AMS 11]
lemma weaklyDivisible_firstPrimesMultiples (N k : ℕ) (hN : 1 ≤ N) :
    WeaklyDivisible k (FirstPrimesMultiples N k) := by
  sorry

/--
Suppose $A \subseteq \{1,\dots,N\}$ is such that there are no $k+1$ elements of $A$ which are
relatively prime. An example is the set of all multiples of the first $k$ primes.
Is this the largest such set?
-/
@[category research solved, AMS 11]
theorem erdos_56 : ∀ᵉ (N ≥ 2) (k), (MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card) ↔
    answer(False) := by
  sorry
