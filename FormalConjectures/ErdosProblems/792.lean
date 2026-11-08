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
# Erdős Problem 792

*References:*
- [erdosproblems.com/792](https://www.erdosproblems.com/792)
- [Ben Green's Open Problem 1](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.1):
  a related question for sets of positive integers; see `Green1.green_1` in
  `FormalConjectures.GreensOpenProblems.«1»`.
- [AlKl90] Alon, N. and Kleitman, D. J., *Sum-free subsets*. A tribute to Paul Erdős (1990),
  13-26.
- [Be25b] Bedert, B., *Large sum-free subsets of sets of integers via $L^1$-estimates for
  trigonometric series*. [arXiv:2502.08624](https://arxiv.org/abs/2502.08624) (2025).
- [Bo97] Bourgain, Jean, *Estimates related to sumfree subsets of sets of integers*. Israel J.
  Math. 97 (1997), 71-92.
- [EGM14] Eberhard, Sean and Green, Ben and Manners, Freddie, *Sets of integers with no large
  sum-free subset*. Ann. of Math. (2) 180 (2014), 621-652.
- [Er65] Erdős, P., *Extremal problems in number theory*. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181-189. [PDF](https://www.renyi.hu/~p_erdos/1965-02.pdf)
- [Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo.,
  1971) (1973), 117-138. [PDF](https://www.renyi.hu/~p_erdos/1973-21.pdf)
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos792

/--
The largest size we can guarantee for a sum-free subset of any set of `n` integers.

Zero is allowed, as in the problem's wording. This gives `f 1 = 0`.
The same number can be used twice in a sum, so `a + a = c` is forbidden too.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {m : ℕ |
    ∀ A : Finset ℤ, A.card = n →
      ∃ B : Finset ℤ,
        B ⊆ A ∧ IsSumFree (B : Set ℤ) ∧ m ≤ B.card}

/-- The set `{0}` has no nonempty sum-free subset, so `f 1 = 0`. -/
@[category test, AMS 5 11]
theorem f_one : f 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold f
  apply csSup_le
  · -- The empty subset shows that zero is a valid guarantee.
    refine ⟨0, ?_⟩
    intro A _
    refine ⟨∅, ?_, ?_, ?_⟩
    · exact Finset.empty_subset A
    · simp [IsSumFree]
    · simp
  · -- Apply the guarantee to {0}, whose only sum-free subset is empty.
    intro m h_guarantee
    obtain ⟨B, h_subset, h_sum_free, h_size⟩ := h_guarantee {0} (by simp)
    have h_cases : B = ∅ ∨ B = {0} :=
      Finset.subset_singleton_iff.mp h_subset
    rcases h_cases with h_empty | h_zero
    · rw [h_empty] at h_size
      simpa using h_size
    · -- But {0} is not sum-free: 0 + 0 = 0.
      rw [h_zero] at h_sum_free
      simp [isSumFree_iff] at h_sum_free

/-- The set `{1, 2}` is not sum-free because `1 + 1 = 2`. -/
@[category test, AMS 5 11]
theorem not_isSumFree_one_two : ¬ IsSumFree ({1, 2} : Set ℤ) := by
  rw [isSumFree_iff]
  norm_num

/-- The set `{1, 3}` is sum-free, even when we use the same number twice. -/
@[category test, AMS 5 11]
theorem isSumFree_one_three : IsSumFree ({1, 3} : Set ℤ) := by
  rw [isSumFree_iff]
  norm_num

def erdos_792.answer : ℕ → ℝ := by
  sorry

/--
Let $f(n)$ be maximal such that in any $A\subset \mathbb{Z}$ with $\lvert A\rvert=n$ there exists
some sum-free subset $B\subseteq A$ with $\lvert B\rvert \geq f(n)$, so that there are no
solutions to
$$a+b=c$$
with $a,b,c\in B$, allowing $a=b$. Estimate $f(n)$.

Since $f(n) = n/3 + o(n)$ is known, we interpret "estimate" as
determining the order of magnitude of the excess $f(n) - n/3$.
-/
@[category research open, question value, AMS 5 11]
theorem erdos_792 :
    (fun n : ℕ => (f n : ℝ) - n / 3) =Θ[atTop] erdos_792.answer := by
  sorry

end Erdos792
