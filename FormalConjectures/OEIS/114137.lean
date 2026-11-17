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
# Difference between first odd semiprime $> 2^n$ and $2^n$

*References:*
- [A114137](https://oeis.org/A114137)
-/

@[expose] public section

namespace OeisA114137
open Nat

/--
The primary defining sequence `a`.
$a(n)$ is the difference between first odd semiprime > $2^n$ and $2^n$.
$$a(n) = \min \{s \mid s > 2^n \text{ and } s \text{ is an odd semiprime}\} - 2^n$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  let m := 2^n
  let s : Set ℕ := { s | s > m ∧ s.IsSemiprime ∧ Odd s }
  sInf s - m

@[category API, AMS 11]
lemma a_eq_of (n val : ℕ)
  (h_mem : val.IsSemiprime ∧ Odd val)
  (h_gt : 2^n < val)
  (h_min : ∀ x, 2^n < x → x < val → ¬ (x.IsSemiprime ∧ Odd x)) :
  a n = val - 2^n := by
  change sInf { s | s > 2^n ∧ s.IsSemiprime ∧ Odd s } - 2^n = val - 2^n
  have h_S : sInf { s | s > 2^n ∧ s.IsSemiprime ∧ Odd s } = val := by
    apply IsLeast.csInf_eq
    constructor
    · exact ⟨h_gt, h_mem⟩
    · rintro x ⟨hx1, hx2⟩
      by_contra! h
      exact h_min x hx1 h hx2
  rw [h_S]

@[category test, AMS 11]
theorem a_1 : a 1 = 7 := by
  apply a_eq_of 1 9 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x <;>
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply]

@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  apply a_eq_of 2 9 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x <;>
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply]

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  apply a_eq_of 3 9 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  apply a_eq_of 4 21 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x <;>
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply]

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  apply a_eq_of 5 33 (by
    norm_num [IsSemiprime, IsAlmostPrime, ArithmeticFunction.cardFactors_apply,
      Nat.primeFactorsList]) (by norm_num)
  intro x h1 h2
  interval_cases x

/--
In this powers of 2 sequence, does 1 occur infinitely often?
-/
@[category research open, question, AMS 11]
theorem conjecture1 :
  Set.Infinite {n : ℕ | a n = 1} := by
  sorry

/-- Counterexample $K$ for `conjecture2`, obtained by the Chinese Remainder Theorem from a
period-$360$ double covering system using $20$ odd primes dividing $2^{360} - 1$ (with $3^2$ and
$5^2$). -/
private def witnessK : ℕ :=
  31578183342437226018483364220022071159573

/-- The $20$ odd primes appearing in the period-$360$ double covering of $2^n + \text{witnessK}$. -/
private def witnessPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 109, 151, 241, 331, 631, 1321, 23311, 61681]

/-- For each residue $r \in \{0, \dots, 359\}$, a pair $(p, q)$ of primes from `witnessPrimes`
such that $p q < \text{witnessK}$, $2^{360} \equiv 1 \pmod{pq}$, and
$2^r + \text{witnessK} \equiv 0 \pmod{pq}$. -/
private def witnessPairs : Array (ℕ × ℕ) := #[
  (3, 3), (5, 5), (3, 73), (11, 13), (3, 7), (5, 31),
  (3, 3), (7, 61681), (3, 19), (5, 331), (3, 7), (17, 41),
  (3, 3), (5, 7), (3, 37), (13, 31), (3, 7), (5, 151),
  (3, 3), (7, 17), (3, 31), (5, 5), (3, 7), (11, 241),
  (3, 3), (5, 7), (3, 19), (13, 17), (3, 7), (5, 73),
  (3, 3), (7, 41), (3, 109), (5, 11), (3, 7), (17, 31),
  (3, 3), (5, 7), (3, 73), (13, 331), (3, 7), (5, 5),
  (3, 3), (7, 11), (3, 19), (5, 31), (3, 7), (73, 151),
  (3, 3), (5, 7), (3, 31), (13, 17), (3, 7), (5, 11),
  (3, 3), (7, 31), (3, 73), (5, 61), (3, 7), (17, 631),
  (3, 3), (5, 5), (3, 19), (11, 13), (3, 7), (5, 31),
  (3, 3), (7, 17), (3, 109), (5, 331), (3, 7), (41, 241),
  (3, 3), (5, 7), (3, 73), (13, 17), (3, 7), (5, 151),
  (3, 3), (7, 1321), (3, 19), (5, 5), (3, 7), (11, 17),
  (3, 3), (5, 7), (3, 37), (13, 61681), (3, 7), (5, 23311),
  (3, 3), (7, 17), (3, 73), (5, 11), (3, 7), (31, 241),
  (3, 3), (5, 7), (3, 19), (13, 17), (3, 7), (5, 5),
  (3, 3), (7, 11), (3, 109), (5, 31), (3, 7), (17, 151),
  (3, 3), (5, 7), (3, 31), (13, 41), (3, 7), (5, 11),
  (3, 3), (7, 17), (3, 19), (5, 61), (3, 7), (73, 241),
  (3, 3), (5, 5), (3, 37), (11, 13), (3, 7), (5, 31),
  (3, 3), (7, 61681), (3, 73), (5, 331), (3, 7), (17, 41),
  (3, 3), (5, 7), (3, 19), (13, 31), (3, 7), (5, 73),
  (3, 3), (7, 17), (3, 31), (5, 5), (3, 7), (11, 241),
  (3, 3), (5, 7), (3, 73), (13, 17), (3, 7), (5, 631),
  (3, 3), (7, 41), (3, 19), (5, 11), (3, 7), (17, 31),
  (3, 3), (5, 7), (3, 37), (13, 331), (3, 7), (5, 5),
  (3, 3), (7, 11), (3, 73), (5, 31), (3, 7), (151, 241),
  (3, 3), (5, 7), (3, 19), (13, 17), (3, 7), (5, 11),
  (3, 3), (7, 31), (3, 109), (5, 61), (3, 7), (17, 23311),
  (3, 3), (5, 5), (3, 73), (11, 13), (3, 7), (5, 31),
  (3, 3), (7, 17), (3, 19), (5, 331), (3, 7), (41, 73),
  (3, 3), (5, 7), (3, 37), (13, 17), (3, 7), (5, 151),
  (3, 3), (7, 1321), (3, 31), (5, 5), (3, 7), (11, 17),
  (3, 3), (5, 7), (3, 19), (13, 61681), (3, 7), (5, 73),
  (3, 3), (7, 17), (3, 109), (5, 11), (3, 7), (31, 241),
  (3, 3), (5, 7), (3, 73), (13, 17), (3, 7), (5, 5),
  (3, 3), (7, 11), (3, 19), (5, 31), (3, 7), (17, 73),
  (3, 3), (5, 7), (3, 31), (13, 41), (3, 7), (5, 11),
  (3, 3), (7, 17), (3, 73), (5, 61), (3, 7), (241, 631),
  (3, 3), (5, 5), (3, 19), (11, 13), (3, 7), (5, 31),
  (3, 3), (7, 61681), (3, 109), (5, 331), (3, 7), (17, 41),
  (3, 3), (5, 7), (3, 73), (13, 31), (3, 7), (5, 151),
  (3, 3), (7, 17), (3, 19), (5, 5), (3, 7), (11, 73),
  (3, 3), (5, 7), (3, 37), (13, 17), (3, 7), (5, 23311),
  (3, 3), (7, 41), (3, 73), (5, 11), (3, 7), (17, 31),
  (3, 3), (5, 7), (3, 19), (13, 331), (3, 7), (5, 5),
  (3, 3), (7, 11), (3, 109), (5, 31), (3, 7), (151, 241),
  (3, 3), (5, 7), (3, 31), (13, 17), (3, 7), (5, 11),
  (3, 3), (7, 31), (3, 19), (5, 61), (3, 7), (17, 73),
  (3, 3), (5, 5), (3, 37), (11, 13), (3, 7), (5, 31),
  (3, 3), (7, 17), (3, 73), (5, 331), (3, 7), (41, 241),
  (3, 3), (5, 7), (3, 19), (13, 17), (3, 7), (5, 73),
  (3, 3), (7, 1321), (3, 31), (5, 5), (3, 7), (11, 17),
  (3, 3), (5, 7), (3, 73), (13, 61681), (3, 7), (5, 631),
  (3, 3), (7, 17), (3, 19), (5, 11), (3, 7), (31, 73),
  (3, 3), (5, 7), (3, 37), (13, 17), (3, 7), (5, 5),
  (3, 3), (7, 11), (3, 73), (5, 31), (3, 7), (17, 151),
  (3, 3), (5, 7), (3, 19), (13, 41), (3, 7), (5, 11),
  (3, 3), (7, 17), (3, 109), (5, 61), (3, 7), (241, 23311)
]

@[category API, AMS 11]
private lemma not_isSemiprime_of_dvd_mul {m p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : p * q ∣ m) (hlt : p * q < m) : ¬ m.IsSemiprime := by
  rcases hdvd with ⟨c, rfl⟩
  have hpq_pos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hc_gt : 1 < c := by
    by_contra hc
    have hle : p * q * c ≤ p * q * 1 := Nat.mul_le_mul_left (p * q) (by omega)
    omega
  have hc_omega : ArithmeticFunction.cardFactors c ≠ 0 := by
    rw [ne_eq, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]
    omega
  rintro ⟨_, hom⟩
  rw [ArithmeticFunction.cardFactors_mul (mul_ne_zero hp.ne_zero hq.ne_zero) (by omega),
    (hp.mul_isAlmostPrime_two hq).2] at hom
  omega

@[category API, AMS 11]
private lemma dvd_two_pow_add_of_mod {d r k n : ℕ}
    (hper : 2 ^ 360 % d = 1) (hres : (2 ^ r + k) % d = 0) (hn : n % 360 = r) :
    d ∣ 2 ^ n + k := by
  apply Nat.dvd_of_mod_eq_zero
  have hsplit : n = 360 * (n / 360) + r := by omega
  rw [hsplit, pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hper, one_pow,
    ← Nat.mul_mod, one_mul, ← Nat.add_mod, hres]

@[category API, AMS 11]
private lemma exists_odd_semiprime_gt (m : ℕ) :
    { s : ℕ | s > m ∧ s.IsSemiprime ∧ Odd s }.Nonempty := by
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (m + 3)
  have hnot2 : ¬ 2 ∣ q := fun h2 ↦ by
    have := hq_prime.eq_one_or_self_of_dvd 2 h2
    omega
  have hq_mod : q % 2 = 1 := by
    rw [Nat.dvd_iff_mod_eq_zero] at hnot2
    omega
  exact ⟨3 * q, by omega, ((by decide : (3 : ℕ).Prime)).mul_isAlmostPrime_two hq_prime,
    ⟨3 * (q / 2) + 1, by omega⟩⟩

/--
Does every odd number occur?

The answer is **no**: using a period-$360$ double covering system formed by $20$ odd primes
dividing $2^{360} - 1$ (together with $3^2$ and $5^2$), the $41$-digit odd integer
$K = 31578183342437226018483364220022071159573$ satisfies, for every $n \in \mathbb{N}$,
$p q \mid 2^n + K$ for a prime pair $(p, q)$ with $p q < K < 2^n + K$. Hence $2^n + K$ has at
least $3$ prime factors counted with multiplicity and is never a semiprime, so $a(n) \ne K$ for
all $n$.
-/
@[category research solved, question, AMS 11]
theorem conjecture2 :
    ¬ ∀ k : ℕ, Odd k → ∃ n : ℕ, a n = k := by
  have hprimes : ∀ p ∈ witnessPrimes, p.Prime := by
    intro p hp
    simp only [witnessPrimes, List.mem_cons] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hnil
    all_goals first | (norm_num; done) | simp at hnil
  have htable : ∀ r : Fin witnessPairs.size,
      let pq := witnessPairs[r]
      pq.1 ∈ witnessPrimes ∧ pq.2 ∈ witnessPrimes ∧ pq.1 * pq.2 < witnessK ∧
        2 ^ 360 % (pq.1 * pq.2) = 1 ∧ (2 ^ r.val + witnessK) % (pq.1 * pq.2) = 0 := by
    decide +kernel
  have hsize : witnessPairs.size = 360 := by decide +kernel
  have hnot_semi : ∀ n : ℕ, ¬ (2 ^ n + witnessK).IsSemiprime := by
    intro n
    let r : Fin witnessPairs.size :=
      ⟨n % 360, Nat.lt_of_lt_of_eq (Nat.mod_lt n (by decide)) hsize.symm⟩
    obtain ⟨hp_mem, hq_mem, hltK, hper, hres⟩ := htable r
    exact not_isSemiprime_of_dvd_mul (hprimes _ hp_mem) (hprimes _ hq_mem)
      (dvd_two_pow_add_of_mod hper hres rfl) (Nat.lt_of_lt_of_le hltK (Nat.le_add_left _ _))
  have hoddK : Odd witnessK := ⟨15789091671218613009241682110011035579786, by norm_num [witnessK]⟩
  intro h
  obtain ⟨n, hn⟩ := h witnessK hoddK
  have hs := Nat.sInf_mem (exists_odd_semiprime_gt (2 ^ n))
  dsimp only [a] at hn
  have heq : sInf { s : ℕ | s > 2 ^ n ∧ s.IsSemiprime ∧ Odd s } = 2 ^ n + witnessK := by
    rw [← hn, Nat.add_sub_of_le (Nat.le_of_lt hs.1)]
  exact hnot_semi n (heq ▸ hs.2.1)

end OeisA114137
