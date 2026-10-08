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
# Erdős Problem 343

*References:*
- [erdosproblems.com/343](https://www.erdosproblems.com/343)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Fo66] Folkman, J., *On the representation of integers as sums of distinct terms from a
  fixed sequence*. Canadian J. Math. 18 (1966), 643-655.
- [SzVu06] Szemerédi, E. and Vu, V., *Long arithmetic progressions in sumsets: thresholds and
  bounds*. J. Amer. Math. Soc. 19 (2006), 119-169.
-/

@[expose] public section

namespace Erdos343

/-- A sequence is subcomplete if its finite subsequence sums contain an infinite arithmetic
progression with positive common difference. Indices represent occurrences, so equal values
at different indices can both be used in a sum. -/
def IsSubcomplete (A : ℕ → ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ subseqSums' A

/-- At least $cN$ occurrences of $A$ have value at most $N$. A finite witness also allows
values with infinite multiplicity. Positivity of the values is a separate hypothesis. -/
def CountAtLeast (A : ℕ → ℕ) (c : ℝ) (N : ℕ) : Prop :=
  ∃ s : Finset ℕ, c * (N : ℝ) ≤ (s.card : ℝ) ∧ ∀ i ∈ s, A i ≤ N

/--
If $A\subseteq \mathbb{N}$ is a multiset of integers such that
$$\lvert A\cap \{1,\ldots,N\}\rvert\gg N$$
for all $N$ then must $A$ be subcomplete? That is, must
$$P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}$$
contain an infinite arithmetic progression?

A problem of Folkman. The original question was answered by Szemerédi and Vu [SzVu06]
(who proved that the answer is yes).

The multiset is represented by a sequence of positive integers. The implicit constant may
depend on the sequence, and the bound is required for every $N\geq 1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_343 : answer(True) ↔
    ∀ A : ℕ → ℕ, (∀ i, 0 < A i) →
      (∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N → CountAtLeast A c N) →
      IsSubcomplete A := by
  sorry

/-- There is a constant $C>0$ such that every infinite nondecreasing sequence of positive
integers with at least $CN$ terms in $\{1,\ldots,N\}$ for all sufficiently large $N$ is
subcomplete [SzVu06, Theorem 6.3]. -/
@[category research solved, AMS 5 11]
theorem erdos_343.variants.szemeredi_vu :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ → ℕ, (∀ i, 0 < A i) → Monotone A →
      (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → CountAtLeast A C N) →
      IsSubcomplete A := by
  sorry

/-- If a positive value occurs infinitely often, its multiples form an infinite arithmetic
progression of finite subsequence sums. -/
@[category textbook, AMS 5 11]
theorem isSubcomplete_of_infinite_occurrences (A : ℕ → ℕ) (v : ℕ) (hv : 0 < v)
    (hinf : {i | A i = v}.Infinite) : IsSubcomplete A := by
  refine ⟨0, v, hv, fun k ↦ ?_⟩
  obtain ⟨t, ht, hcard⟩ := hinf.exists_subset_card_eq k
  refine ⟨t, ?_⟩
  rw [Finset.sum_congr rfl (fun i hi ↦ (ht hi : A i = v)), Finset.sum_const, hcard,
    smul_eq_mul, zero_add]

@[category test, AMS 5 11]
theorem count_succ (N : ℕ) : CountAtLeast (fun i ↦ i + 1) 1 N := by
  refine ⟨Finset.range N, ?_, fun i hi ↦ ?_⟩
  · simp
  · simp only [Finset.mem_range] at hi
    change i + 1 ≤ N
    omega

@[category test, AMS 5 11]
theorem zero_mem_subseqSums (A : ℕ → ℕ) : 0 ∈ subseqSums' A := by
  exact ⟨∅, by simp⟩

@[category test, AMS 5 11]
theorem repeated_terms : 2 ∈ subseqSums' (fun _ : ℕ ↦ 1) := by
  exact ⟨{0, 1}, by simp⟩

@[category test, AMS 5 11]
theorem not_isSubcomplete_zero : ¬ IsSubcomplete (fun _ : ℕ ↦ 0) := by
  rintro ⟨a, d, hd, hAP⟩
  obtain ⟨s, hs⟩ := hAP 1
  simp at hs
  omega

end Erdos343
