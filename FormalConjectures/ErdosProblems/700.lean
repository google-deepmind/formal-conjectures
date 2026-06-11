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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 700

*Reference:* [erdosproblems.com/700](https://www.erdosproblems.com/700)

Let
$$f(n) = \min_{1 < k \le n/2} \gcd\left(n, \binom{n}{k}\right).$$

* **(a)** Characterise those composite $n$ such that $f(n) = n / P(n)$, where $P(n)$ is the
  largest prime dividing $n$.
* **(b)** Are there infinitely many composite $n$ such that $f(n) > n^{1/2}$?
* **(c)** Is it true that, for every composite $n$, $f(n) \ll_A n / (\log n)^A$ for every $A > 0$?

This is a problem of Erdős and Szekeres [ErSz78], who introduce `f`, record the facts
`f(p^a) = p` and `f(pq) = p` (formalised below as `erdos_700.variants.prime_pow` and
`erdos_700.variants.prime_mul`), compute e.g. `f(30) = 6`, note strict examples such as
`30, 70, 154`, remark that they cannot prove there are infinitely many composite `n` with
`f(n) > n^{1/2}` (part (b)), and prove the bound `f(n) ≤ (1 + o(1)) n / \log n`. The sequence
`f` is [OEIS A091963](https://oeis.org/A091963) (see also Guy, *Unsolved Problems in Number
Theory*, B31, B33). All three parts are recorded as open on erdosproblems.com.

[ErSz78] Erdős, P. and Szekeres, G., _Some number theoretic problems on binomial coefficients_.
Austral. Math. Soc. Gaz. (1978), 97-99.
-/

namespace Erdos700

open Finset

/-- `f n = min_{1 < k ≤ n/2} gcd(n, C(n,k))`. (The infimum is `0` when the range is empty, i.e.
`n < 4`.) -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

/-- `P n` is the largest prime factor of `n` (and `0` if `n ≤ 1`). -/
noncomputable def P (n : ℕ) : ℕ := n.primeFactors.sup id

/-- The set whose infimum defines `f`. -/
def fSet (n : ℕ) : Set ℕ := {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

/-- `f n` unfolds to the infimum of `fSet n`. -/
@[category API, AMS 11]
lemma f_eq (n : ℕ) : f n = sInf (fSet n) := rfl

/-- Each `gcd(n, C(n,k))` with `1 < k ≤ n/2` belongs to `fSet n`. -/
@[category API, AMS 11]
lemma f_mem (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    Nat.gcd n (n.choose k) ∈ fSet n := ⟨k, h1, h2, rfl⟩

/-- `f n` is a lower bound: `f n ≤ gcd(n, C(n,k))` for every `1 < k ≤ n/2`. -/
@[category API, AMS 11]
lemma f_le (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    f n ≤ Nat.gcd n (n.choose k) := Nat.sInf_le (f_mem n k h1 h2)

/-- **(a)** Characterise those composite `n` with `f(n) = n / P(n)`. The characterisation itself
is open; we state it as the (unknown) predicate that is equivalent to being such an `n`. -/
@[category research open, AMS 11]
theorem erdos_700.parts.i (n : ℕ) (hn : ¬ n.Prime) (hn1 : 1 < n) :
    f n = n / P n ↔ answer(sorry) := by
  sorry

/-- **(b)** There are infinitely many composite `n` such that `f(n) > n^{1/2}`, equivalently
`f(n)^2 > n`. -/
@[category research open, AMS 11]
theorem erdos_700.parts.ii : {n : ℕ | ¬ n.Prime ∧ 1 < n ∧ (f n) ^ 2 > n}.Infinite := by
  sorry

/-- **(c)** For every `A > 0`, `f(n) ≪_A n / (log n)^A` over all composite `n`: there is a constant
`C` (depending on `A`) with `f(n) ≤ C · n / (log n)^A` for every composite `n`. -/
@[category research open, AMS 11]
theorem erdos_700.parts.iii :
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ¬ n.Prime → 1 < n →
      (f n : ℝ) ≤ C * (n : ℝ) / (Real.log n) ^ A) ↔ answer(sorry) := by
  sorry

/- ## Proven partial results toward (a) -/

/-- Lucas (one step): for prime `P ∣ n`, if `P ∤ C(n,k)` then `P ∣ k`. -/
@[category API, AMS 11]
lemma prime_dvd_of_not_dvd_choose (P n k : ℕ) (hP : P.Prime) (hPn : P ∣ n)
    (h : ¬ P ∣ n.choose k) : P ∣ k := by
  haveI := Fact.mk hP
  by_contra hk
  apply h
  have hmod : n.choose k ≡ (n % P).choose (k % P) * (n / P).choose (k / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hn0 : n % P = 0 := by
    have h := (Nat.modEq_zero_iff_dvd).2 hPn; simpa [Nat.ModEq, Nat.zero_mod] using h
  have hkP : 0 < k % P := Nat.pos_of_ne_zero (fun hh => hk (Nat.dvd_of_mod_eq_zero hh))
  rw [hn0, Nat.choose_eq_zero_of_lt hkP, zero_mul] at hmod
  exact (Nat.modEq_zero_iff_dvd).1 hmod

/-- `f(p^a) = p` for a prime `p` and `a ≥ 2` (recorded by Erdős–Szekeres [ErSz78]). In particular,
since `(p^a) / P(p^a) = p^{a-1}`, the prime power `p^a` is a "hit" (`f(n) = n / P(n)`) if and only
if `a = 2`. -/
@[category research solved, AMS 11]
theorem erdos_700.variants.prime_pow (p a : ℕ) (hp : p.Prime) (ha : 2 ≤ a) : f (p ^ a) = p := by
  have hp2 : 2 ≤ p := hp.two_le
  set k := p ^ (a - 1) with hk
  have hk0 : k ≠ 0 := (pow_pos hp.pos _).ne'
  have hkn : k ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
  have hk1 : 1 < k := by
    calc 1 < p := hp.one_lt
      _ ≤ k := Nat.le_self_pow (by omega) p
  have hk2 : k ≤ p ^ a / 2 := by
    have hpa : p ^ a = p * k := by rw [hk, ← pow_succ']; congr 1; omega
    have : 2 * k ≤ p ^ a := by rw [hpa]; exact Nat.mul_le_mul_right _ hp2
    omega
  have hknne : k ≠ p ^ a := by
    rw [hk]; intro h; exact absurd (Nat.pow_right_injective hp2 h) (by omega)
  have hcpos : 0 < (p ^ a).choose k := Nat.choose_pos hkn
  have hkfact : k.factorization p = a - 1 := by
    rw [hk, Nat.factorization_pow, Nat.Prime.factorization hp]; simp
  have hvp : ((p ^ a).choose k).factorization p = 1 := by
    rw [Nat.factorization_choose_prime_pow hp hkn hk0, hkfact]; omega
  have hgcd : Nat.gcd (p ^ a) ((p ^ a).choose k) = p := by
    obtain ⟨j, hja, hjeq⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_left (p ^ a) ((p ^ a).choose k))
    have hpC : p ∣ (p ^ a).choose k := hp.dvd_choose_pow hk0 hknne
    have hpg : p ∣ p ^ j := by
      rw [← hjeq]; exact Nat.dvd_gcd (dvd_pow_self p (by omega)) hpC
    have hp2C : ¬ (p ^ 2 ∣ (p ^ a).choose k) := by
      rw [hp.pow_dvd_iff_le_factorization hcpos.ne', hvp]; omega
    have hp2g : ¬ (p ^ 2 ∣ p ^ j) := by
      rw [← hjeq]; exact fun h => hp2C (h.trans (Nat.gcd_dvd_right _ _))
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [pow_zero, Nat.dvd_one] at hpg; omega
      · exact hj0
    have hj2 : j ≤ 1 := by
      by_contra h; push_neg at h
      exact hp2g ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).2 h)
    rw [hjeq, show j = 1 from by omega, pow_one]
  have hle : f (p ^ a) ≤ p := by
    have hh := f_le (p ^ a) k hk1 hk2; rwa [hgcd] at hh
  have hge : p ≤ f (p ^ a) := by
    have hne : (fSet (p ^ a)).Nonempty := ⟨_, f_mem (p ^ a) k hk1 hk2⟩
    obtain ⟨j, hj1, hj2, hjeq⟩ := Nat.sInf_mem hne
    have hjne : j ≠ p ^ a := by rintro rfl; omega
    have hpdvd : p ∣ Nat.gcd (p ^ a) ((p ^ a).choose j) :=
      Nat.dvd_gcd (dvd_pow_self p (by omega)) (hp.dvd_choose_pow (by omega) hjne)
    calc p ≤ Nat.gcd (p ^ a) ((p ^ a).choose j) :=
            Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (pow_pos hp.pos a)) hpdvd
      _ = sInf (fSet (p ^ a)) := hjeq.symm
      _ = f (p ^ a) := (f_eq _).symm
  omega

/-- `f(pq) = p` for distinct primes `p < q` (recorded by Erdős–Szekeres [ErSz78]); in particular
`pq` is always a "hit" (`f(pq) = pq / P(pq) = p`). Proof via Lucas' theorem:
`p ∤ C(pq,k) ⟹ p ∣ k` (and the same for `q`),
so any `k` with `gcd(pq, C(pq,k)) = 1` must be a multiple of `pq`, of which there are none in
`(1, pq/2]`; the witness `k = q` gives `gcd(pq, C(pq,q)) = p`. -/
@[category research solved, AMS 11]
theorem erdos_700.variants.prime_mul (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    f (p * q) = p := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hpndq : ¬ p ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hp hq).1 h; omega
  have hk1 : 1 < q := by omega
  have hk2 : q ≤ p * q / 2 := by
    have : 2 * q ≤ p * q := by nlinarith
    omega
  have hpC : p ∣ (p * q).choose q := by
    by_contra h
    exact hpndq (prime_dvd_of_not_dvd_choose p (p * q) q hp ⟨q, rfl⟩ h)
  have hqC : ¬ q ∣ (p * q).choose q := by
    have hmod : (p * q).choose q ≡
        ((p * q) % q).choose (q % q) * ((p * q) / q).choose (q / q) [MOD q] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    rw [Nat.mul_mod_left, Nat.mod_self, Nat.choose_zero_right,
        Nat.mul_div_cancel _ (by omega : 0 < q), Nat.div_self (by omega : 0 < q),
        Nat.choose_one_right, one_mul] at hmod
    intro hdvd
    have h0 : (p * q).choose q ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).2 hdvd
    have hp0 : q ∣ p := (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans h0)
    have := Nat.le_of_dvd (by omega) hp0
    omega
  have hgcd : Nat.gcd (p * q) ((p * q).choose q) = p := by
    have hpg : p ∣ Nat.gcd (p * q) ((p * q).choose q) := Nat.dvd_gcd ⟨q, rfl⟩ hpC
    obtain ⟨e, he⟩ := hpg
    have hgdvd : Nat.gcd (p * q) ((p * q).choose q) ∣ p * q := Nat.gcd_dvd_left _ _
    rw [he] at hgdvd
    have hedvd : e ∣ q := (Nat.mul_dvd_mul_iff_left (by omega : 0 < p)).1 hgdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq e hedvd) with he1 | heq
    · rw [he, he1, mul_one]
    · exfalso
      have hqg : q ∣ Nat.gcd (p * q) ((p * q).choose q) := by rw [he, heq]; exact ⟨p, by ring⟩
      exact hqC (hqg.trans (Nat.gcd_dvd_right _ _))
  have hle : f (p * q) ≤ p := by have := f_le (p * q) q hk1 hk2; rwa [hgcd] at this
  have hge : p ≤ f (p * q) := by
    have hne : (fSet (p * q)).Nonempty := ⟨_, f_mem (p * q) q hk1 hk2⟩
    obtain ⟨k, hk1', hk2', hkeq⟩ := Nat.sInf_mem hne
    rw [f_eq, hkeq]
    set g := Nat.gcd (p * q) ((p * q).choose k) with hgdef
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by positivity)
    have hg1 : g ≠ 1 := by
      intro hg
      have hpnd : ¬ p ∣ (p * q).choose k := fun hd => by
        have : p ∣ g := Nat.dvd_gcd ⟨q, rfl⟩ hd
        rw [hg] at this; exact absurd (Nat.le_of_dvd one_pos this) (by omega)
      have hqnd : ¬ q ∣ (p * q).choose k := fun hd => by
        have : q ∣ g := Nat.dvd_gcd ⟨p, by ring⟩ hd
        rw [hg] at this; exact absurd (Nat.le_of_dvd one_pos this) (by omega)
      have hpk : p ∣ k := prime_dvd_of_not_dvd_choose p (p * q) k hp ⟨q, rfl⟩ hpnd
      have hqk : q ∣ k := prime_dvd_of_not_dvd_choose q (p * q) k hq ⟨p, by ring⟩ hqnd
      have hpqk : p * q ∣ k := Nat.Coprime.mul_dvd_of_dvd_of_dvd
        ((Nat.coprime_primes hp hq).2 (by omega)) hpk hqk
      have hkpos : 0 < k := by omega
      have h1 : p * q ≤ k := Nat.le_of_dvd hkpos hpqk
      have h2 : k ≤ p * q / 2 := hk2'
      omega
    have hgdvd : g ∣ p * q := Nat.gcd_dvd_left _ _
    obtain ⟨P, hP, hPg⟩ := Nat.exists_prime_and_dvd hg1
    have hPpq : P ∣ p * q := hPg.trans hgdvd
    have hPpq2 : P = p ∨ P = q := by
      rcases (hP.dvd_mul.1 hPpq) with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hP hp).1 h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hP hq).1 h)
    have hPge : p ≤ P := by rcases hPpq2 with rfl | rfl <;> omega
    have hPleg : P ≤ g := Nat.le_of_dvd hgpos hPg
    omega
  omega

end Erdos700
