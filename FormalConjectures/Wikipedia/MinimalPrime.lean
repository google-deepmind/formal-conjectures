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
# Minimal primes in radix bases

Fix an integer base $b \ge 2$. A prime $p$ is *minimal in base $b$* if no proper subsequence (not
necessarily contiguous) of its canonical base-$b$ expansion represents a prime—equivalently, no
prime $q \neq p$ has its canonical base-$b$ digit list as a sublist of `Nat.digits b p`. By
Higman's lemma, the set of minimal primes in base $b$ is finite for every $b \ge 2$. Jeffrey
Shallit (2000) classified all $26$ base-$10$ minimal primes (`OEIS A071062`, up to $66600049$).
Curtis Bright, Raymond Devillers, and Shallit (2016) extended minimal-prime classifications to
larger bases; in base $17$, they already reduced the classification to $1279$ minimal probable
primes (not all certified prime) together with the single unresolved candidate family
$\mathrm{F}1\{9\}$ (base-$17$ digits $15, 1, 9, \dots, 9$).

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Minimal_prime_(recreational_mathematics))
- [OEIS A071062](https://oeis.org/A071062)
- J. Shallit, *Minimal primes*, J. Recreational Math. **30** (1999–2000), 113–117.
- C. Bright, R. Devillers, and J. Shallit, *Minimal elements for the prime numbers*, Exp. Math.
  **25** (2016), 321–331.
-/

@[expose] public section

namespace MinimalPrime

/-- Prime $p$ is minimal in base $b \ge 2$ when no prime $q \neq p$ has `Nat.digits b q` as a
sublist of `Nat.digits b p`. -/
def IsMinimalPrimeInBase (b p : ℕ) : Prop :=
  2 ≤ b ∧ p.Prime ∧ ¬∃ q : ℕ, q.Prime ∧ q ≠ p ∧ (Nat.digits b q).Sublist (Nat.digits b p)

/-- Base $10$ includes $2$ as minimal and excludes $13$ (via proper sublist $3$), while bases
$b \in \{0, 1\}$ are excluded. -/
@[category test, AMS 11 68]
theorem two_minimal_and_thirteen_not_minimal_base_ten :
    IsMinimalPrimeInBase 10 2 ∧
      ¬IsMinimalPrimeInBase 10 13 ∧
      ¬IsMinimalPrimeInBase 0 2 ∧
      ¬IsMinimalPrimeInBase 1 2 := by
  refine ⟨⟨by omega, Nat.prime_two, ?_⟩, ?_, fun h => by have := h.1; omega,
    fun h => by have := h.1; omega⟩
  · rintro ⟨q, hq, hne, hsub⟩
    have hd : Nat.digits 10 2 = [2] := by decide
    rw [hd, List.sublist_singleton] at hsub
    rcases hsub with h0 | h2
    · exact hq.ne_zero (Nat.digits_eq_nil_iff_eq_zero.mp h0)
    · have := congrArg (Nat.ofDigits 10) h2
      rw [Nat.ofDigits_digits] at this
      exact hne this
  · rintro ⟨_, _, hno⟩
    exact hno ⟨3, by decide, by decide, by decide⟩

/-- Single-digit primes $p \in \{3, 5, 7\}$ satisfy `IsMinimalPrimeInBase 10 p`, whereas $1$
satisfies `¬ IsMinimalPrimeInBase b 1` for every $b$. -/
@[category test, AMS 11 68]
theorem single_digit_primes_minimal_base_ten :
    IsMinimalPrimeInBase 10 3 ∧
    IsMinimalPrimeInBase 10 5 ∧
    IsMinimalPrimeInBase 10 7 ∧
    ∀ b : ℕ, ¬ IsMinimalPrimeInBase b 1 := by
  have hmin : ∀ p : ℕ, p.Prime → p < 10 → IsMinimalPrimeInBase 10 p := by
    intro p hp hlt
    refine ⟨by omega, hp, ?_⟩
    rintro ⟨q, hq, hne, hsub⟩
    have hd : Nat.digits 10 p = [p] := Nat.digits_of_lt 10 p hp.ne_zero hlt
    rw [hd, List.sublist_singleton] at hsub
    rcases hsub with h0 | hp_eq
    · exact hq.ne_zero (Nat.digits_eq_nil_iff_eq_zero.mp h0)
    · have := congrArg (Nat.ofDigits 10) hp_eq
      rw [Nat.ofDigits_digits, Nat.ofDigits_singleton] at this
      exact hne this
  exact ⟨hmin 3 (by decide) (by omega), hmin 5 (by decide) (by omega),
    hmin 7 (by decide) (by omega), fun _ h => Nat.not_prime_one h.2.1⟩

/-- In binary ($b = 2$), $2 = (10)_2$ is minimal, whereas in base $10$ neither $23$ nor $37$ is
minimal. -/
@[category test, AMS 11 68]
theorem binary_two_minimal_and_base_ten_nonminimal :
    IsMinimalPrimeInBase 2 2 ∧
    ¬ IsMinimalPrimeInBase 10 23 ∧
    ¬ IsMinimalPrimeInBase 10 37 := by
  refine ⟨⟨by omega, Nat.prime_two, ?_⟩, ?_, ?_⟩
  · rintro ⟨q, hq, hne, hsub⟩
    have hd : Nat.digits 2 2 = [0, 1] := by decide
    rw [hd] at hsub
    have hval : q = Nat.ofDigits 2 (Nat.digits 2 q) := (Nat.ofDigits_digits 2 q).symm
    rcases List.sublist_cons_iff.mp hsub with hsub1 | ⟨l, hdig, hsub1⟩
    · rcases List.sublist_singleton.mp hsub1 with h0 | h1
      · rw [h0] at hval; rw [hval] at hq; revert hq; decide
      · rw [h1] at hval; rw [hval] at hq; revert hq; decide
    · rcases List.sublist_singleton.mp hsub1 with h0 | h1
      · rw [hdig, h0] at hval; rw [hval] at hq; revert hq; decide
      · rw [hdig, h1] at hval; rw [hval] at hne; revert hne; decide
  · rintro ⟨_, _, hno⟩
    exact hno ⟨3, by decide, by decide, by decide⟩
  · rintro ⟨_, _, hno⟩
    exact hno ⟨7, by decide, by decide, by decide⟩

/-- Finiteness of minimal primes (empty for $b < 2$, and finite by Higman's lemma for $b \ge 2$):
for every $b \in \mathbb{N}$, the set of primes satisfying `IsMinimalPrimeInBase b p` is finite. -/
@[category textbook, AMS 11 68]
theorem minimal_primes_finite_in_every_base (b : ℕ) :
    {p : ℕ | IsMinimalPrimeInBase b p}.Finite := by
  sorry

/-- Base-$10$ classification (Shallit 2000): exactly $26$ primes satisfy
`IsMinimalPrimeInBase 10 p`. -/
@[category research solved, AMS 11 68]
theorem base_ten_minimal_primes_card :
    {p : ℕ | IsMinimalPrimeInBase 10 p}.ncard = 26 := by
  sorry

/-- Explicit base-$10$ minimal prime set (Shallit 2000, `OEIS A071062`): the primes satisfying
`IsMinimalPrimeInBase 10 p` are precisely the $26$ integers listed below. -/
@[category research solved, AMS 11 68]
theorem base_ten_minimal_primes_eq :
    {p : ℕ | IsMinimalPrimeInBase 10 p} =
      {2, 3, 5, 7, 11, 19, 41, 61, 89, 409, 449, 499, 881, 991, 6469, 6949, 9001, 9049, 9649,
        9949, 60649, 666649, 946669, 60000049, 66000049, 66600049} := by
  sorry

/-- Unresolved base-$17$ candidate family $\mathrm{F}1\{9\}$: does there exist $k \in \mathbb{N}$
such that the integer with base-$17$ digits $15, 1, \underbrace{9, \dots, 9}_{k}$ (namely
$15 \cdot 17^{k + 1} + 17^k + \sum_{i < k} 9 \cdot 17^i$) satisfies
`IsMinimalPrimeInBase 17`? -/
@[category research open, question, AMS 11 68]
theorem base_seventeen_f19_family_minimal_prime_question :
    ∃ k : ℕ, IsMinimalPrimeInBase 17
      (15 * 17 ^ (k + 1) + 17 ^ k + ∑ i ∈ Finset.range k, 9 * 17 ^ i) := by
  sorry

end MinimalPrime
