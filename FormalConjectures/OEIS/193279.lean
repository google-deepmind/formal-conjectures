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
# Number of distinct sums of distinct proper divisors of $n$

The sequence $a(n)$ counts the number of distinct sums of non-empty subsets of the proper divisors
of $n$.

*References:*
- [A193279](https://oeis.org/A193279)
-/

@[expose] public section

namespace OeisA193279

/--
Number of distinct sums of distinct proper divisors of $n$ (excluding the empty sum $0$).
-/
def a (n : ℕ) : ℕ :=
  (n.properDivisors.powerset.image (fun s : Finset ℕ => ∑ x ∈ s, x)).card - 1

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

@[category test, AMS 11]
theorem a_6 : a 6 = 6 := by decide

/--
If $n$ is an even perfect number, then $a(n) = n$.
- _Michael Engling_, Jul 20 2011
-/
@[category textbook, AMS 11]
theorem a_eq_self_of_perfect_of_even (n : ℕ) (hperf : n.Perfect) (heven : Even n) :
    a n = n := by
  sorry

/-- The subset sums of a disjoint union are the sums of a subset sum of each part. -/
@[category API, AMS 11]
private lemma image_sum_powerset_union {s t : Finset ℕ} (h : Disjoint s t) :
    (s ∪ t).powerset.image (fun u => ∑ x ∈ u, x) =
      Finset.image₂ (· + ·) (s.powerset.image fun u => ∑ x ∈ u, x)
        (t.powerset.image fun u => ∑ x ∈ u, x) := by
  ext m
  simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_image₂]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨_, ⟨u ∩ s, Finset.inter_subset_right, rfl⟩, _,
      ⟨u ∩ t, Finset.inter_subset_right, rfl⟩, ?_⟩
    rw [← Finset.sum_union (h.mono Finset.inter_subset_right Finset.inter_subset_right),
      ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hu]
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u ∪ v, Finset.union_subset_union hu hv, Finset.sum_union (h.mono hu hv)⟩

/--
Is the converse true, i.e., if $a(n) = n$, is $n$ necessarily an even perfect number?
- _Michael Engling_, Jul 20 2011

The answer is no: for example, $n = 492 = 2^2 \cdot 3 \cdot 41$ and
$n = 1652 = 2^2 \cdot 7 \cdot 59$ satisfy $a(n) = n$ but are abundant rather than perfect.
-/
@[category research solved, question, AMS 11]
theorem conjecture : ¬ ∀ n : ℕ, 0 < n → a n = n → n.Perfect ∧ Even n := by
  intro h
  -- `n = 492` has `a 492 = 492`, but its proper divisors sum to `684`. The subset sums of the
  -- proper divisors of `492` are the numbers `i + 41 * j` with `i < 29` and `j < 17`.
  have hdiv : Nat.properDivisors 492 = {1, 2, 3, 4, 6, 12} ∪ {41, 82, 123, 164, 246} := by
    decide +kernel
  have hdisj : Disjoint ({1, 2, 3, 4, 6, 12} : Finset ℕ) {41, 82, 123, 164, 246} := by decide
  have h1 : ({1, 2, 3, 4, 6, 12} : Finset ℕ).powerset.image (fun u => ∑ x ∈ u, x) =
      Finset.range 29 := by decide +kernel
  have h2 : ({41, 82, 123, 164, 246} : Finset ℕ).powerset.image (fun u => ∑ x ∈ u, x) =
      (Finset.range 17).image (41 * ·) := by decide +kernel
  have hinj : (Finset.range 29 ×ˢ Finset.range 17 : Set (ℕ × ℕ)).InjOn
      fun p => p.1 + 41 * p.2 := by
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    simp only [Set.mem_prod, Finset.coe_range, Set.mem_Iio] at hij hij'
    simp only [Prod.mk.injEq]
    dsimp only at h
    omega
  have h492 : a 492 = 492 := by
    rw [a, hdiv, image_sum_powerset_union hdisj, h1, h2, Finset.image₂_image_right,
      Finset.card_image₂_iff.mpr hinj, Finset.card_range, Finset.card_range]
  have hperf := (h 492 (by norm_num) h492).1
  rw [Nat.perfect_iff_sum_properDivisors (by norm_num)] at hperf
  revert hperf
  decide +kernel

end OeisA193279
