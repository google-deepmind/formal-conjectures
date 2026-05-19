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
theorem maxWeaklyDivisible_zero : ∀ k : ℕ, MaxWeaklyDivisible 0 k = 0 := by
  intro k
  simp [MaxWeaklyDivisible, Nat.sSup_def]

@[category test, AMS 11]
theorem maxWeaklyDivisible_one {k : ℕ} (hk : k ≠ 0) : MaxWeaklyDivisible 1 k = 1 := by
  have : {x | ∃ A, WeaklyDivisible k A ∧ (A = ∅ ∨ A = {1}) ∧ #A = x} = {0, 1} := by
    refine Set.ext fun _ => ⟨fun _ => by aesop, ?_⟩
    rintro ⟨_, _⟩
    · simpa using weaklyDivisible_empty k
    · exact ⟨{1}, by simp_all [weaklyDivisible_singleton hk 1]⟩
  simp_all [MaxWeaklyDivisible]

@[category test, AMS 11]
theorem maxWeaklyDivisible_zero_k (N : ℕ) : MaxWeaklyDivisible N 0 = 0 := by
  simp [empty_iff_weaklyDivisible_zero, MaxWeaklyDivisible]

/--
`FirstPrimesMultiples N k` is the set of numbers in `{1,..., N}` that are
a multiple of one of the first `k` primes.
-/
noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
    (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)

@[category test, AMS 11]
theorem firstPrimesMultiples_one_card_zero (k : ℕ) : (FirstPrimesMultiples 1 k).card = 0 := by
  simp [FirstPrimesMultiples, Finset.filter_singleton]
  intro n h
  by_contra hprime
  have : Nat.Prime 1 := by
    convert Nat.prime_nth_prime n
    exact hprime.symm
  tauto

@[category test, AMS 11]
theorem firstPrimesMultiples_zero_k_card_zero (N : ℕ) : (FirstPrimesMultiples N 0).card = 0 := by
  simp [FirstPrimesMultiples]

/--
An example of a `k`-weakly divisible set is the subset of `{1, ..., N}`
containing the multiples of the first `k` primes.
-/
@[category API, AMS 11]
lemma weaklyDivisible_firstPrimesMultiples (N k : ℕ) :
    WeaklyDivisible k (FirstPrimesMultiples N k) := by
  unfold WeaklyDivisible
  intro s hs
  rw [Finset.mem_powersetCard] at hs
  -- Define the map from s to Fin k
  set f : s → Fin k := fun ⟨x, hx⟩ =>
    have h_exists := (Finset.mem_filter.mp (hs.1 hx)).2
    ⟨Classical.choose h_exists, (Classical.choose_spec h_exists).1⟩
  have hcard_s : Fintype.card s = k + 1 := by simp [hs.2]
  have hcard_fink : Fintype.card (Fin k) = k := Fintype.card_fin k
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by omega)
  intro h_pair
  have hne_val : x.1 ≠ y.1 := by
    intro h_eq
    exact hne (Subtype.ext h_eq)
  have h_coprime := h_pair x.2 y.2 hne_val
  set p := (f x).val.nth Nat.Prime
  have hp_prime : p.Prime := Nat.prime_nth_prime _
  have hp_div_x : p ∣ x.1 := by
    have h_exists := (Finset.mem_filter.mp (hs.1 x.2)).2
    exact (Classical.choose_spec h_exists).2
  have hp_div_y : p ∣ y.1 := by
    have h_exists := (Finset.mem_filter.mp (hs.1 y.2)).2
    have h_eq_f : (f x).val = (f y).val := by rw [heq]
    -- (f y).val is Classical.choose h_exists by definition
    have : p = (Classical.choose h_exists).nth Nat.Prime := by
      dsimp [p]
      rw [h_eq_f]
    rw [this]
    exact (Classical.choose_spec h_exists).2
  have hp_div_gcd : p ∣ x.1.gcd y.1 := Nat.dvd_gcd hp_div_x hp_div_y
  have h_gcd_eq_one : x.1.gcd y.1 = 1 := h_coprime
  rw [h_gcd_eq_one] at hp_div_gcd
  have hp_le_one : p ≤ 1 := Nat.le_of_dvd (by norm_num) hp_div_gcd
  have : p > 1 := hp_prime.one_lt
  omega

/--
Suppose $A \subseteq \{1,\dots,N\}$ is such that there are no $k+1$ elements of $A$ which are
relatively prime. An example is the set of all multiples of the first $k$ primes.
Is this the largest such set?  To avoid trivial counterexamples, we must insist that $N$ be at
least the $k$th prime.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos56.lean"]
theorem erdos_56 : answer(False) ↔ ∀ᵉ (k > 0) (N ≥ (k-1).nth Nat.Prime),
    (MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card) := by
  sorry

end Erdos56
