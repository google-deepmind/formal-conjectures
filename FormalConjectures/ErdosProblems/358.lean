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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 358

*References:*
- [erdosproblems.com/358](https://www.erdosproblems.com/358)
- [Ta26] T. Tao, [Erdős problem 358](https://terrytao.wordpress.com/wp-content/uploads/2026/02/erdos-358-2.pdf) (2026)
-/

@[expose] public section

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

@[category API, AMS 11]
private theorem two_mul_sum_Icc (u v : ℕ) :
    2 * ∑ i ∈ Icc u v, i = (v + 1 - u) * (u + v) := by
  by_cases huv : u ≤ v
  · rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range (fun i : ℕ => i)]
    rw [sum_add_distrib (f := fun _ => u) (g := fun i => i), sum_const, card_range, Nat.nsmul_eq_mul]
    have h := sum_range_id_mul_two (v + 1 - u)
    have hs : v + 1 - u - 1 + 2 * u = u + v := by omega
    nlinarith only [h, congrArg ((v + 1 - u) * ·) hs]
  · rw [Icc_eq_empty (by omega), sum_empty, show v + 1 - u = 0 by omega]
    simp

private abbrev FactorPairs (n : ℕ) :=
  {p : ℕ × ℕ // p.1 < p.2 ∧ p.1 % 2 ≠ p.2 % 2 ∧ p.1 * p.2 = 2 * n}

-- The two factors are the length of the interval and the sum of its endpoints.
private def intervalEquivFactorPairs {n : ℕ} (hn : 0 < n) :
    intervalRepresentations id n ≃ FactorPairs n where
  toFun := by
    rintro ⟨⟨u, v⟩, hu, hv, hsum⟩
    have huv : u ≤ v := by
      by_contra! h
      simp [Icc_eq_empty (not_le.mpr h), Nat.ne_of_gt hn] at hsum
    exact ⟨(v + 1 - u, u + v), by dsimp; omega, by dsimp; omega,
      by rw [← two_mul_sum_Icc]; exact congrArg (2 * ·) hsum.symm⟩
  invFun := by
    rintro ⟨⟨l, s⟩, hls, hp, hprod⟩
    dsimp at hls hp hprod
    have hl : 0 < l := Nat.pos_of_ne_zero fun h => by simp [h, Nat.ne_of_gt hn] at hprod
    refine ⟨((s + 1 - l) / 2, (s + l - 1) / 2), by omega, by omega, ?_⟩
    have hlen : (s + l - 1) / 2 + 1 - (s + 1 - l) / 2 = l := by omega
    have hsum : (s + 1 - l) / 2 + (s + l - 1) / 2 = s := by omega
    have h := two_mul_sum_Icc ((s + 1 - l) / 2) ((s + l - 1) / 2)
    rw [hlen, hsum, hprod] at h
    exact (Nat.eq_of_mul_eq_mul_left (by decide) h).symm
  left_inv := by
    rintro ⟨⟨u, v⟩, hu, hv, hsum⟩
    have huv : u ≤ v := by
      by_contra! h
      simp [Icc_eq_empty (not_le.mpr h), Nat.ne_of_gt hn] at hsum
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> omega
  right_inv := by
    rintro ⟨⟨l, s⟩, hls, hp, hprod⟩
    dsimp at hls hp hprod
    have hl : 0 < l := Nat.pos_of_ne_zero fun h => by simp [h, Nat.ne_of_gt hn] at hprod
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> omega

@[category API, AMS 11]
private theorem oddFactor_dvd_and_complement {n d e : ℕ} (hp : d * e = 2 * n)
    (hd : Odd d) (he : ¬ Odd e) : d ∣ n ∧ 2 * (n / d) = e := by
  rw [Nat.odd_iff] at hd he
  have he' : e = 2 * (e / 2) := by omega
  have hn : n = d * (e / 2) := by nlinarith only [hp, congrArg (d * ·) he']
  exact ⟨⟨e / 2, hn⟩, by rw [hn, Nat.mul_div_cancel_left _ (by omega), ← he']⟩

private def oddDivisorsEquivFactorPairs {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.filter Odd : Finset ℕ) ≃ FactorPairs n where
  toFun := by
    rintro ⟨d, hd⟩
    have hdvd := (Finset.mem_filter.mp hd).1
    have hmod := Nat.odd_iff.mp (Finset.mem_filter.mp hd).2
    let e := 2 * (n / d)
    have he : e % 2 = 0 := by dsimp [e]; omega
    have hprod : d * e = 2 * n := by
      rw [show d * e = 2 * (n / d * d) by dsimp [e]; ac_rfl,
        Nat.div_mul_cancel (Nat.mem_divisors.mp hdvd).1]
    refine ⟨(min d e, max d e), ?_⟩
    dsimp
    rcases le_total d e with h | h
    · rw [min_eq_left h, max_eq_right h]
      exact ⟨by omega, by omega, hprod⟩
    · rw [min_eq_right h, max_eq_left h]
      exact ⟨by omega, by omega, (mul_comm e d).trans hprod⟩
  invFun := by
    rintro ⟨⟨l, s⟩, h⟩
    refine ⟨if Odd l then l else s, ?_⟩
    obtain ⟨_, hp, hprod⟩ := h
    dsimp at hp hprod
    simp only [Finset.mem_filter, Nat.mem_divisors]
    split_ifs with h
    · have hs : ¬ Odd s := by simp only [Nat.odd_iff] at h ⊢; omega
      exact ⟨⟨(oddFactor_dvd_and_complement hprod h hs).1, hn⟩, h⟩
    · have hs : Odd s := by simp only [Nat.odd_iff] at h ⊢; omega
      exact ⟨⟨(oddFactor_dvd_and_complement ((mul_comm s l).trans hprod) hs h).1, hn⟩, hs⟩
  left_inv := by
    rintro ⟨d, hd⟩
    have ho := (Finset.mem_filter.mp hd).2
    have he : ¬ Odd (2 * (n / d)) := by simp [Nat.odd_iff]
    apply Subtype.ext
    change (if Odd (min d (2 * (n / d))) then min d (2 * (n / d)) else max d (2 * (n / d))) = d
    rcases le_total d (2 * (n / d)) with h | h
    · simp [min_eq_left h, ho]
    · simp [min_eq_right h, max_eq_left h, he]
  right_inv := by
    rintro ⟨⟨l, s⟩, hls, hp, hprod⟩
    dsimp at hls hp hprod
    apply Subtype.ext
    by_cases h : Odd l
    · have hs : ¬ Odd s := by simp only [Nat.odd_iff] at h ⊢; omega
      change (min (if Odd l then l else s) _, max (if Odd l then l else s) _) = (l, s)
      simp [h, (oddFactor_dvd_and_complement hprod h hs).2, min_eq_left hls.le, max_eq_right hls.le]
    · have hs : Odd s := by simp only [Nat.odd_iff] at h ⊢; omega
      change (min (if Odd l then l else s) _, max (if Odd l then l else s) _) = (l, s)
      simp [h, (oddFactor_dvd_and_complement ((mul_comm s l).trans hprod) hs h).2,
        min_eq_right hls.le, max_eq_left hls.le]

/--
When $A_n = n$, the function $f$ counts the odd divisors of each positive integer $n$.
At $n = 0$, the representation set is infinite and `Nat.divisors 0` is empty, so both counts are $0$.
-/
@[category textbook, AMS 5 11]
theorem f_id : f id = fun n ↦ #{d ∈ n.divisors | Odd d} := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hinf : (intervalRepresentations id 0).Infinite := by
      refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k + 2, 1)) ?_ ?_
      · intro a b h
        have := congrArg Prod.fst h
        dsimp at this
        omega
      · intro k
        exact ⟨by omega, by decide, by simp⟩
    rw [f, @Nat.card_eq_zero_of_infinite _ hinf.to_subtype]
    simp
  · rw [f, Nat.card_congr (intervalEquivFactorPairs hn |>.trans
      (oddDivisorsEquivFactorPairs hn.ne').symm)]
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]

set_option linter.style.formal_proof_palomar false in
/--
Let $A=\{a_1 < \cdots\}$ be an infinite sequence of integers. Let $f(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$
Is there such an $A$ for which $f(n)\to \infty$ as $n\to \infty$?

Tao [Ta26] constructed such a sequence with $f(n) \gg \log n$ for all sufficiently large $n$.
-/
@[category research solved, question, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos358.lean#L9111"]
theorem erdos_358.parts.i :
    ∃ A, StrictMono A ∧ atTop.Tendsto (f A) atTop := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
Let $A=\{a_1 < \cdots\}$ be an infinite sequence of integers. Let $f(n)$ count the number of
solutions to $$n=\sum_{u\leq i\leq v}a_i.$$
Is there an $A$ such that $f(n)\geq 2$ for all large $n$?

This also follows from Tao's construction with $f(n) \gg \log n$ [Ta26].
-/
@[category research solved, question, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos358.lean#L9115"]
theorem erdos_358.parts.ii :
    ∃ A, StrictMono A ∧ ∀ᶠ n in atTop, 2 ≤ f A n := by
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
  obtain ⟨A, hA, hf⟩ := erdos_358.parts.ii
  refine ⟨A, hA, ?_⟩
  filter_upwards [hf, eventually_gt_atTop 0] with n hn hn₀
  exact one_le_g_of_two_le_f hA hn₀ hn


end Erdos358
