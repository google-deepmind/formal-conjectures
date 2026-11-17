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
  [PDF](https://web.math.princeton.edu/~nalon/PDFS/Publications2/Sum-free%20subsets.pdf)
- [Be25b] Bedert, B., *Large sum-free subsets of sets of integers via $L^1$-estimates for
  trigonometric series*. [arXiv:2502.08624](https://arxiv.org/abs/2502.08624) (2025).
- [Bo97] Bourgain, Jean, *Estimates related to sumfree subsets of sets of integers*. Israel J.
  Math. 97 (1997), 71-92.
- [EGM14] Eberhard, Sean and Green, Ben and Manners, Freddie, *Sets of integers with no large
  sum-free subset*. Ann. of Math. (2) 180 (2014), 621-652.
  [arXiv:1301.4579](https://arxiv.org/abs/1301.4579)
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
  apply csSup_le'
  intro m h_guarantee
  obtain ⟨B, h_subset, h_sum_free, h_size⟩ := h_guarantee {0} (by simp)
  rcases Finset.subset_singleton_iff.mp h_subset with h_empty | h_zero
  · simpa [h_empty] using h_size
  · rw [h_zero] at h_sum_free
    simp [isSumFree_iff] at h_sum_free

/-- The definition gives the elementary bound $f(|A|) \leq |A|$: a subset of $A$
cannot have more elements than $A$. -/
@[category API, AMS 5 11]
theorem f_le_card (A : Finset ℤ) : f A.card ≤ A.card := by
  apply csSup_le'
  intro m hm
  obtain ⟨B, hBA, _, hmB⟩ := hm A rfl
  exact hmB.trans (Finset.card_le_card hBA)

/-- Every two-element set contains a nonzero element, while $\{0,1\}$ has no
sum-free subset of size two. Thus the definition gives $f(2)=1$. -/
@[category test, AMS 5 11]
theorem f_two : f 2 = 1 := by
  apply le_antisymm
  · apply csSup_le'
    intro m hm
    obtain ⟨B, hBA, hB, hmB⟩ := hm {0, 1} (by simp)
    have h0 : (0 : ℤ) ∉ B := by
      intro h0
      exact isSumFree_iff.mp hB 0 h0 0 h0 (by simpa using h0)
    have hsub : B ⊆ {1} := by
      intro x hx
      have := hBA hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      exact this.resolve_left (fun h => h0 (h ▸ hx))
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  · apply le_csSup
    · refine ⟨2, ?_⟩
      intro m hm
      obtain ⟨B, hBA, _, hmB⟩ := hm {0, 1} (by simp)
      exact hmB.trans (by simpa using Finset.card_le_card hBA)
    · intro A hA
      obtain ⟨a, ha, ha0⟩ := Finset.exists_mem_ne (by omega : 1 < A.card) 0
      refine ⟨{a}, Finset.singleton_subset_iff.mpr ha, ?_, by simp⟩
      simp only [isSumFree_iff, Finset.coe_singleton, Set.mem_singleton_iff]
      intro x hx y hy
      subst x
      subst y
      omega

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

/-- The unknown growth rate $h$ for which $f(n)-n/3=\Theta(h(n))$.
The relation $=\Theta[\mathrm{atTop}]$ means that the absolute values bound each
other up to positive constant factors for all sufficiently large $n$. -/
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

/--
Erdős [Er65, Theorem 2] gave a simple proof that shows $f(n) \geq n/3$.

For the literal integer domain, which allows zero, assume $n \geq 2$.
The case $A=\{0\}$ would otherwise be a counterexample.
-/
@[category research solved, AMS 5 11]
theorem erdos_792.variants.erdos :
    ∀ A : Finset ℤ, 2 ≤ A.card →
      ∃ B ⊆ A, IsSumFree (B : Set ℤ) ∧ A.card ≤ 3 * B.card := by
  sorry

/--
Alon and Kleitman [AlKl90, Proposition 1.1] improved this to $f(n)\geq (n+1)/3$.

Their result concerns nonempty sets of nonzero integers. For the function `f`,
which allows zero, apply this to the set after removing zero.
-/
@[category research solved, AMS 5 11]
theorem erdos_792.variants.alon_kleitman :
    ∀ A : Finset ℤ, 0 ∉ A → A.Nonempty →
      ∃ B ⊆ A, IsSumFree (B : Set ℤ) ∧ A.card + 1 ≤ 3 * B.card := by
  sorry

/--
Bourgain [Bo97] further improved this to $(n+2)/3$.

As recorded in [EGM14, Introduction], this holds for sets of nonzero integers
of size at least three. The restriction is necessary: $\{1,2\}$ has no
sum-free subset of size two.
-/
@[category research solved, AMS 5 11]
theorem erdos_792.variants.bourgain :
    ∀ A : Finset ℤ, 0 ∉ A → 3 ≤ A.card →
      ∃ B ⊆ A, IsSumFree (B : Set ℤ) ∧ A.card + 2 ≤ 3 * B.card := by
  sorry

/--
The best lower bound known is $f(n)\geq n/3+c\log\log n$ for some constant
$c>0$, due to Bedert [Be25b, Theorem 1.2]. We state this for sufficiently
large $n$, avoiding the undefined logarithms in the paper's small cases.
-/
@[category research solved, AMS 5 11]
theorem erdos_792.variants.bedert :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 3 + c * Real.log (Real.log n) ≤ (f n : ℝ) := by
  sorry

/--
The best upper bound known is $f(n) \leq n/3+o(n)$, due to Eberhard, Green,
and Manners [EGM14, Theorem 1.1]. Equivalently, for every $\varepsilon>0$,
eventually $f(n)\leq (1/3+\varepsilon)n$.
-/
@[category research solved, AMS 5 11]
theorem erdos_792.variants.eberhard_green_manners :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (f n : ℝ) ≤ (1 / 3 + ε) * n := by
  sorry

/-- Alon and Kleitman's bound [AlKl90] implies the classical bound [Er65]
even when the ambient set contains zero: remove it before applying the improvement. -/
@[category test, AMS 5 11]
theorem erdos_792.variants.alon_kleitman_implies_erdos :
    type_of% erdos_792.variants.alon_kleitman →
    type_of% erdos_792.variants.erdos := by
  intro h A hA
  by_cases h0 : 0 ∈ A
  · have hcard := Finset.card_erase_add_one h0
    have hne : (A.erase 0).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨B, hBA, hB, hcardB⟩ := h (A.erase 0) (Finset.notMem_erase _ _) hne
    exact ⟨B, hBA.trans (Finset.erase_subset _ _), hB, by omega⟩
  · obtain ⟨B, hBA, hB, hcardB⟩ := h A h0 (Finset.card_pos.mp (by omega))
    exact ⟨B, hBA, hB, by omega⟩

end Erdos792
