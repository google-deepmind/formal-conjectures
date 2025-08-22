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

open scoped Finset

/-!
# Erdős Problem 56

*Reference:* [erdosproblems.com/56](https://www.erdosproblems.com/56)
-/

namespace Erdos56

/--
Say a set of natural numbers is `k`-weakly divisible if any `k+1` elements
of `A` are not relatively prime.
-/
def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
    ∀ s ∈ A.powersetCard (k + 1), ¬ Set.Pairwise s Nat.Coprime

@[category API, AMS 11]
lemma weaklyDivisible_empty (k : ℕ): WeaklyDivisible k {} := by
  simp [WeaklyDivisible]

/-- A singleton is `k`-weakly divisble if `k ≠ 0`. -/
@[category API, AMS 11]
lemma weaklyDivisible_singleton {k : ℕ} (hk : k ≠ 0) (l : ℕ) : WeaklyDivisible k {l} := by
  simp [WeaklyDivisible, hk]

/-- No non-empty set is `1`-weakly divisible. -/
@[category API, AMS 11]
lemma not_weaklyDivisible_zero {A : _} (h : A.Nonempty) : ¬WeaklyDivisible 0 A := by
  simpa [WeaklyDivisible] using ⟨{_}, by simpa using h.choose_spec⟩

@[category API, AMS 11]
lemma empty_iff_weaklyDivisible_zero {A : _} : WeaklyDivisible 0 A ↔ A = ∅ :=
  ⟨fun h ↦ Finset.not_nonempty_iff_eq_empty.1 <| mt not_weaklyDivisible_zero (not_not.2 h),
    fun h ↦ h ▸ weaklyDivisible_empty _⟩

/--
`MaxWeaklyDivisible N k` is the size of the largest k-weakly divisible subset of `{1,..., N}`
-/
noncomputable def MaxWeaklyDivisible (N : ℕ) (k : ℕ) : ℕ :=
  sSup {#A | (A : Finset ℕ) (_ : A ⊆ Finset.Icc 1 N) (_ : WeaklyDivisible k A)}

@[category test, AMS 11]
example (k : ℕ) : MaxWeaklyDivisible 0 k = 0 := by
  simp [MaxWeaklyDivisible, Nat.sSup_def]

@[category test, AMS 11]
example {k : ℕ} (hk : k ≠ 0) : MaxWeaklyDivisible 1 k = 1 := by
  have : {x | ∃ A, WeaklyDivisible k A ∧ (A = ∅ ∨ A = {1}) ∧ #A = x} = {0, 1} := by
    refine Set.ext fun _ => ⟨fun _ => by aesop, ?_⟩
    rintro ⟨_, _⟩
    · simpa using weaklyDivisible_empty k
    · exact ⟨{1}, by simp_all [weaklyDivisible_singleton hk 1]⟩
  simp_all [MaxWeaklyDivisible]

@[category test, AMS 11]
example (N : ℕ) : MaxWeaklyDivisible N 0 = 0 := by
  simp [empty_iff_weaklyDivisible_zero, MaxWeaklyDivisible]

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

@[category test, AMS 11]
example (N : ℕ) : (FirstPrimesMultiples N 0).card = 0 := by
  simp [FirstPrimesMultiples]

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
theorem erdos_56 : (∀ᵉ (N ≥ 2) (k > 0), (MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card)) ↔
    answer(False) := by
  sorry

end Erdos56
