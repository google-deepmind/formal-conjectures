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
# Erdős Problem 913

*Reference:* [erdosproblems.com/913](https://www.erdosproblems.com/913)

Reviewed by @b-mehta on 2025-05-27
-/

namespace Erdos913

/--
Are there infinitely many $n$ such that if
$$
  n(n + 1) = \prod_i p_i^{k_i}
$$
is the factorisation into distinct primes then all exponents $k_i$ are distinct?
-/
@[category research open, AMS 11]
theorem erdos_913 :
    { n | Set.InjOn (n * (n + 1)).factorization (n * (n + 1)).primeFactors }.Infinite ↔
    answer(sorry) := by
  sorry

/--
It is likely that there are infinitely many primes $p$ such that $8p^2 - 1$ is also prime.
-/
@[category research open, AMS 11]
theorem erdos_913.variants.infinite_many_8p_sq_add_one_primes :
    { p | p.Prime ∧ (8 * p ^ 2 - 1).Prime }.Infinite := by
  sorry

/-- If there are infinitely many primes $p$ such that $8p^2 - 1$ is prime, then this is true. -/
@[category research solved, AMS 11]
theorem erdos_913.variants.conditional (h : { p | p.Prime ∧ (8 * p ^ 2 - 1).Prime }.Infinite) :
    { n | Set.InjOn (n * (n + 1)).factorization (n * (n + 1)).primeFactors }.Infinite := by
  set S := { p | p.Prime ∧ (8 * p ^ 2 - 1).Prime }
  let f : ℕ → ℕ := fun p ↦ 8 * p ^ 2 - 1
  have hS : ∀ p, p.Prime → 1 < 8 * p ^ 2 := by
    rintro p hp
    nlinarith [hp.two_le]
  have : S.InjOn f := by
    simp only [Set.InjOn, f]
    rintro a ha b hb h
    rw [tsub_left_inj (hS a ha.1).le (hS b hb.1).le] at h
    simpa using h
  refine ((h.diff (Set.finite_singleton 2)).image (this.mono Set.diff_subset)).mono ?_
  simp only [Set.image_subset_iff, Set.preimage_setOf_eq, S]
  rintro p ⟨⟨hp, hp'⟩, hp''⟩
  simp only [Set.mem_singleton_iff] at hp''
  have fac : (f p * (f p + 1)).factorization =
      Finsupp.single (8 * p ^ 2 - 1) 1 + (Finsupp.single p 2 + Finsupp.single 2 3) := by
    simp only [f, Nat.sub_add_cancel (hS p hp).le]
    have : 2 ≤ p := hp.two_le
    rw [Nat.factorization_mul hp'.ne_zero (by positivity),
      Nat.factorization_mul (by positivity) (by positivity), hp'.factorization,
      hp.factorization_pow, (show 8 = 2 ^ 3 from rfl), Nat.prime_two.factorization_pow,
      add_comm (Finsupp.single 2 3)]
  have aux₂ : (fun₀ | 2 => 3).support = {2} := by simp [Finsupp.support_eq_singleton]
  have aux₁ : ((fun₀ | p => 2) + fun₀ | 2 => 3).support = {p, 2} := by
    rw [Finsupp.support_single_add (by simp [aux₂, hp'']) (by simp), Finset.cons_eq_insert, aux₂]
  have aux₃ : p + 1 < 8 * p ^ 2 := by
    replace hp := hp.two_le
    zify at hp ⊢
    linear_combination (8 * p + 15 : ℤ) * hp
  have aux₄ : 8 * p ^ 2 - 1 ≠ p := by
    rw [ne_eq, tsub_eq_iff_eq_add_of_le (hS p hp).le]
    exact aux₃.ne'
  have aux₅ : 8 * p ^ 2 - 1 ≠ 2 := by
    omega
  have pf : (f p * (f p + 1)).primeFactors = {8 * p ^ 2 - 1, p, 2} := by
    rw [← Nat.support_factorization, fac, Finsupp.support_single_add _ (by simp),
      Finset.cons_eq_insert, aux₁]
    simp [*]
  simp only [Set.mem_setOf_eq]
  rw [fac, pf]
  simp only [Finsupp.coe_add, Finset.coe_insert, Finset.coe_singleton]
  rw [Set.injOn_insert (by simp [*]), Set.injOn_insert (by simp [hp''])]
  simp [aux₄, hp'', Ne.symm, aux₅]

end Erdos913
