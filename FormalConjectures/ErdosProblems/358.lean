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

import FormalConjecturesUtil

/-!
# Erdős Problem 358

*References:*
- [erdosproblems.com/358](https://www.erdosproblems.com/358)
- [Ta26] T. Tao, [Erdős problem 358](https://terrytao.wordpress.com/wp-content/uploads/2026/02/erdos-358-2.pdf) (2026)
-/

namespace Erdos358

open Filter Finset

/-
Let $a$ be an infinite sequence of integers. `intervalRepresentations A n` is the set of solutions
to $$n=\sum_{u\leq i\leq v}a_i.$$ where `u` and `v` are positive integers.
-/
def intervalRepresentations (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, A i}

/-
Let $a$ be an infinite sequence of integers. Let $f(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$
-/
noncomputable def f (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentations A n)

/-
Let $a$ be an infinite sequence of integers. `intervalRepresentationsNonTrivial A n` is the set of
solutions to $$n=\sum_{u\leq i\leq v}a_i$$ such that the sum has at least two terms.
-/
def intervalRepresentationsNonTrivial (A : ℕ → ℕ) (n : ℕ) : Set (ℕ × ℕ) :=
  {(u, v) | 0 < u ∧ 0 < v ∧ u < v ∧ n = ∑ i ∈ Icc u v, A i}

/-
Let $a$ be an infinite sequence of integers. Let $g(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$ such that the sum has at least two terms.
-/
noncomputable def g (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card (intervalRepresentationsNonTrivial A n)

/--
When $A_n = n$, the function $f$ defined above counts the number of odd divisors of $n$.
-/
@[category textbook, AMS 5 11]
theorem f_id : f id = fun n ↦ #{d ∈ n.divisors | Odd d} := by
  sorry

/--
Let $A=\{a_1 < \cdots\}$ be an infinite sequence of integers. Let $f(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$
Is there such an $A$ for which $f(n)\to \infty$ as $n\to \infty$?

Tao [Ta26] constructed such a sequence with $f(n) \gg \log n$ for all sufficiently large $n$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos358.lean#L9111"]
theorem erdos_358.parts.i :
    answer(True) ↔ ∃ A, StrictMono A ∧ atTop.Tendsto (f A) atTop := by
  sorry

/--
Let $A=\{a_1 < \cdots\}$ be an infinite sequence of integers. Let $f(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$
Is there an $A$ such that $f(n)\geq 2$ for all large $n$?

This also follows from Tao's construction with $f(n) \gg \log n$ [Ta26].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos358.lean#L9115"]
theorem erdos_358.parts.ii :
    answer(True) ↔ ∃ A, StrictMono A ∧ ∀ᶠ n in atTop, 2 ≤ f A n := by
  sorry

/--
When $A =\{a_1 < \cdots\}$ corresponds to the set of primes, it is conjectured that the
$\limsup$ of the number of representations $$n=\sum_{u\leq i\leq v}a_i$$ is infinite.
-/
@[category research open, AMS 5 11]
theorem erdos_358.variants.prime_set :
    atTop.limsup (fun n ↦ (f (Nat.nth Nat.Prime) n : ℕ∞)) = ⊤ := by
  sorry

/--
When $A =\{a_1 < \cdots\}$ corresponds to the set of primes, it is conjectured that the set of
numbers $n$ that have representations $$n=\sum_{u\leq i\leq v}a_i$$ has positive upper density.
-/
@[category research open, AMS 5 11]
theorem erdos_358.variants.prime_set_density_representation :
    0 < {n : ℕ | intervalRepresentations (Nat.nth Nat.Prime) n |>.Nonempty}.upperDensity := by
  sorry

/--
If $A$ is strictly increasing then any $n > 0$ has at most one representation
$$n=\sum_{u\leq i\leq v}a_i$$ with a single term, so discarding the single-term representations
loses at most one solution.
-/
@[category API, AMS 5 11]
theorem one_le_g_of_two_le_f {A : ℕ → ℕ} (hA : StrictMono A) {n : ℕ} (hn : 0 < n)
    (hf : 2 ≤ f A n) : 1 ≤ g A n := by
  classical
  have hfin : (intervalRepresentations A n).Finite := by
    rcases Set.finite_or_infinite (intervalRepresentations A n) with h | h
    · exact h
    · rw [f, @Nat.card_eq_zero_of_infinite _ h.to_subtype] at hf
      omega
  have hsub : intervalRepresentationsNonTrivial A n ⊆ intervalRepresentations A n := by
    rintro ⟨u, v⟩ hr
    simp only [intervalRepresentationsNonTrivial, Set.mem_ofPred_eq] at hr
    simp only [intervalRepresentations, Set.mem_ofPred_eq]
    exact ⟨hr.1, hr.2.1, hr.2.2.2⟩
  refine (Set.ncard_pos (hfin.subset hsub)).mpr ?_
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  -- Without a representation of length at least two, every representation is a single term.
  have key : ∀ r ∈ intervalRepresentations A n, r.1 = r.2 ∧ A r.1 = n := by
    rintro ⟨u, v⟩ hr
    simp only [intervalRepresentations, Set.mem_ofPred_eq] at hr
    obtain ⟨hu, hv, hsum⟩ := hr
    have hle : u ≤ v := by
      by_contra hc
      rw [Finset.Icc_eq_empty hc, Finset.sum_empty] at hsum
      omega
    have huv : u = v := by
      rcases eq_or_lt_of_le hle with h | h
      · exact h
      · exact absurd (Set.eq_empty_iff_forall_notMem.mp hempty (u, v)
          (by simp only [intervalRepresentationsNonTrivial, Set.mem_ofPred_eq]
              exact ⟨hu, hv, h, hsum⟩)) (by simp)
    subst huv
    exact ⟨rfl, by simpa using hsum.symm⟩
  -- Injectivity of `A` then makes that single term unique, contradicting `2 ≤ f A n`.
  have := hfin.to_subtype
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.one_lt_ncard_iff_nontrivial.mp hf
  obtain ⟨hp₁, hpn⟩ := key p hp
  obtain ⟨hq₁, hqn⟩ := key q hq
  exact hpq (Prod.ext (hA.injective (hpn.trans hqn.symm))
    (by rw [← hp₁, ← hq₁]; exact hA.injective (hpn.trans hqn.symm)))

/--
In [ErGr80] Erdős and Graham further asked whether there is an $A$ with $f(n)\geq 1$ for all
large $n$. Egami observed that this holds trivially for $a_n=n$, so they may have intended to
count only those representations $$n=\sum_{u\leq i\leq v}a_i$$ that use at least two consecutive
terms, which is what $g$ counts.

This follows from Tao's construction [Ta26], which gives $f(n)\gg\log n$: see
`erdos_358.parts.ii` and `one_le_g_of_two_le_f`.
-/
@[category research solved, AMS 5 11]
theorem erdos_358.variants.one_le :
    ∃ A, StrictMono A ∧ ∀ᶠ n in atTop, 1 ≤ g A n := by
  obtain ⟨A, hA, hf⟩ := erdos_358.parts.ii.mp trivial
  refine ⟨A, hA, ?_⟩
  filter_upwards [hf, eventually_gt_atTop 0] with n hn hn₀
  exact one_le_g_of_two_le_f hA hn₀ hn


end Erdos358
