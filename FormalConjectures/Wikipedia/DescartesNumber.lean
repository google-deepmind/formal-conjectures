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
# Descartes Numbers

A *Descartes number* (or spoof odd perfect integer) is an odd integer $n = m \cdot w$ where $w$ is
composite (`Nat.Composite`), $\gcd(m, w) = 1$, and $\sigma_1(m)(w + 1) = 2 m w$, so treating $w$ as
a prime factor would yield $\sigma_1(n) = 2n$. René Descartes (1638) found
$$D = 3^2 \cdot 7^2 \cdot 11^2 \cdot 13^2 \cdot 22021 = 198{,}585{,}576{,}189,$$
with composite spoof factor $22021 = 19^2 \cdot 61$; no further example is known [KW91]. Banks,
Güloğlu, Nevans, and Saidak [BGNS08] proved that $D$ is the unique cube-free Descartes integer with
fewer than seven distinct prime divisors and that every cube-free Descartes integer coprime to $3$
has over $10^6$ distinct prime divisors; Tóth [To21] showed that any other Descartes factorization
$n = m \cdot w \ne D$ satisfies $m > 10^{12}$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Descartes_number)
- [KW91] V. Klee and S. Wagon (1991), Dolciani Math. Expositions **11**, Math. Assoc. America.
- [BGNS08] W. D. Banks, A. M. Güloğlu, C. W. Nevans, and F. Saidak (2008), CRM Proc. Lecture Notes
  **46**, Amer. Math. Soc., 167–173.
- [To21] L. Tóth (2021), Comput. Methods Sci. Technol. **27**, no. 1, 25–31.
-/

@[expose] public section

namespace DescartesNumber

open scoped ArithmeticFunction.sigma

/-- Descartes's 1638 example $3^2 \cdot 7^2 \cdot 11^2 \cdot 13^2 \cdot 22021 =
198{,}585{,}576{,}189$. -/
def descartesExample : ℕ := 198585576189

/-- `(m, w)` is a Descartes factorization if $w$ is composite (`Nat.Composite`), $m \cdot w$ is odd,
$\gcd(m, w) = 1$, and $\sigma_1(m)(w + 1) = 2 m w$ (which together force $m > 1$). -/
def IsDescartesFactorization (m w : ℕ) : Prop :=
  w.Composite ∧ Odd (m * w) ∧ Nat.Coprime m w ∧ σ 1 m * (w + 1) = 2 * m * w

/-- `IsDescartesNumber n` holds when $n = m \cdot w$ for some `IsDescartesFactorization m w`. -/
def IsDescartesNumber (n : ℕ) : Prop :=
  ∃ m w : ℕ, n = m * w ∧ IsDescartesFactorization m w

/-- Every Descartes number is odd and strictly greater than $1$. -/
@[category API, AMS 11]
theorem isDescartesNumber_odd_and_gt_one {n : ℕ} (h : IsDescartesNumber n) :
    Odd n ∧ 1 < n := by
  rcases h with ⟨m, w, rfl, ⟨hw1, _⟩, hodd, _⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun hm => by simp [hm] at hodd
  exact ⟨hodd, by nlinarith⟩

/-- For any odd integer $m$ satisfying $\sigma_1(m) = 2m - 1$ (almost perfect, cf.
`AlmostPerfectNumbers`) such that $2m - 1$ is composite, the product $m(2m - 1)$ satisfies
`IsDescartesNumber`. -/
@[category API, AMS 11]
theorem isDescartesNumber_of_odd_almostPerfect {m : ℕ} (hodd : Odd m)
    (hap : σ 1 m = 2 * m - 1) (hcomp : (2 * m - 1).Composite) :
    IsDescartesNumber (m * (2 * m - 1)) := by
  have hm1 : 1 < m := by have := hcomp.1; omega
  refine ⟨m, 2 * m - 1, rfl, hcomp, ?_, ?_, ?_⟩
  · refine hodd.mul ?_
    rcases hodd with ⟨k, rfl⟩
    exact ⟨2 * k, by omega⟩
  · have hcop : Nat.Coprime m (2 * m - 1) := by
      have h1 : (2 * m - 1) + 1 = 2 * m := by omega
      rw [Nat.coprime_iff_gcd_eq_one]
      have hdvd1 : Nat.gcd m (2 * m - 1) ∣ 2 * m :=
        (Nat.gcd_dvd_left m (2 * m - 1)).trans ⟨2, by ring⟩
      have hdvd2 : Nat.gcd m (2 * m - 1) ∣ 2 * m - 1 := Nat.gcd_dvd_right m (2 * m - 1)
      have hdvd_diff : Nat.gcd m (2 * m - 1) ∣ 2 * m - (2 * m - 1) := Nat.dvd_sub hdvd1 hdvd2
      rwa [show 2 * m - (2 * m - 1) = 1 by omega, Nat.dvd_one] at hdvd_diff
    exact hcop
  · rw [hap]
    have : 2 * m - 1 + 1 = 2 * m := by omega
    rw [this]
    ring

/-- Descartes's classical integer `descartesExample` satisfies `IsDescartesNumber`. -/
@[category test, AMS 11]
theorem isDescartesNumber_descartesExample : IsDescartesNumber descartesExample := by
  refine ⟨3 ^ 2 * 7 ^ 2 * 11 ^ 2 * 13 ^ 2, 22021, by norm_num [descartesExample],
    ⟨by norm_num, ?_⟩, ⟨99292788094, by norm_num⟩, by norm_num, ?_⟩
  · intro hp
    rcases hp.eq_one_or_self_of_dvd 361 ⟨61, by norm_num⟩ with h | h <;> omega
  · have hmul := ArithmeticFunction.isMultiplicative_sigma (k := 1)
    have hs1 : σ 1 (3 ^ 2 * (7 ^ 2 * (11 ^ 2 * 13 ^ 2))) =
        σ 1 (3 ^ 2) * (σ 1 (7 ^ 2) * (σ 1 (11 ^ 2) * σ 1 (13 ^ 2))) := by
      rw [hmul.map_mul_of_coprime (by norm_num), hmul.map_mul_of_coprime (by norm_num),
        hmul.map_mul_of_coprime (by norm_num)]
    have h3 : σ 1 (3 ^ 2) = 13 := by
      rw [ArithmeticFunction.sigma_apply_prime_pow (by norm_num : Nat.Prime 3)]; norm_num
    have h7 : σ 1 (7 ^ 2) = 57 := by
      rw [ArithmeticFunction.sigma_apply_prime_pow (by norm_num : Nat.Prime 7)]; norm_num
    have h11 : σ 1 (11 ^ 2) = 133 := by
      rw [ArithmeticFunction.sigma_apply_prime_pow (by norm_num : Nat.Prime 11)]; norm_num
    have h13 : σ 1 (13 ^ 2) = 183 := by
      rw [ArithmeticFunction.sigma_apply_prime_pow (by norm_num : Nat.Prime 13)]; norm_num
    rw [show 3 ^ 2 * 7 ^ 2 * 11 ^ 2 * 13 ^ 2 = 3 ^ 2 * (7 ^ 2 * (11 ^ 2 * 13 ^ 2)) by norm_num,
      hs1, h3, h7, h11, h13]
    norm_num

/-- `descartesExample` is cube-free (`Powerfree 3 descartesExample`). -/
@[category test, AMS 11]
theorem powerfree_three_descartesExample : Powerfree 3 descartesExample := by
  intro x hx
  rw [Nat.isUnit_iff]
  by_contra hx1
  obtain ⟨q, hqp, hqdvd⟩ := Nat.exists_prime_and_dvd hx1
  have hq3 : q ^ 3 ∣ 3 ^ 2 * 7 ^ 2 * 11 ^ 2 * 13 ^ 2 * 19 ^ 2 * 61 :=
    (pow_dvd_pow_of_dvd hqdvd 3).trans (by simpa [descartesExample] using hx)
  have hqd : q ∣ 3 ^ 2 * 7 ^ 2 * 11 ^ 2 * 13 ^ 2 * 19 ^ 2 * 61 :=
    (dvd_pow_self q (by decide : 3 ≠ 0)).trans hq3
  have hp_abs {p : ℕ} (hp : p.Prime) (h : q ∣ p ^ 2)
      (hnp : ¬ p ^ 3 ∣ 3 ^ 2 * 7 ^ 2 * 11 ^ 2 * 13 ^ 2 * 19 ^ 2 * 61) : False := by
    rcases hp.eq_one_or_self_of_dvd q (hqp.dvd_of_dvd_pow h) with rfl | rfl
    · exact hqp.ne_one rfl
    · exact hnp hq3
  simp only [hqp.dvd_mul] at hqd
  rcases hqd with (((((h | h) | h) | h) | h) | h61)
  iterate 5 exact hp_abs (by norm_num) h (by norm_num)
  rcases (by norm_num : Nat.Prime 61).eq_one_or_self_of_dvd q h61 with rfl | rfl
  · exact hqp.ne_one rfl
  · norm_num at hq3

/-- **Banks–Güloğlu–Nevans–Saidak Theorem** [BGNS08]: every cube-free Descartes integer not
divisible by $3$ has strictly more than $10^6$ distinct prime factors. -/
@[category research solved, AMS 11]
theorem descartes_cubeFree_not_dvd_three_primeFactors_gt_million (n : ℕ)
    (hd : IsDescartesNumber n) (hcf : Powerfree 3 n) (h3 : ¬ 3 ∣ n) :
    10 ^ 6 < n.primeFactors.card := by
  sorry

/-- **Tóth's Lower Bound on Spoof Factorizations** [To21]: every Descartes factorization
$m \cdot w \ne 198{,}585{,}576{,}189$ satisfies $m > 10^{12}$. -/
@[category research solved, AMS 11]
theorem descartes_non_example_factor_gt_ten_pow_twelve (m w : ℕ)
    (hf : IsDescartesFactorization m w) (hne : m * w ≠ descartesExample) :
    10 ^ 12 < m := by
  sorry

/-- **Banks–Güloğlu–Nevans–Saidak Uniqueness Theorem** [BGNS08] (see also [To21, §1]):
$198{,}585{,}576{,}189$ is the unique cube-free Descartes integer with fewer than seven distinct
prime divisors. -/
@[category research solved, AMS 11]
theorem descartes_cubeFree_lt_seven_primeFactors_unique (n : ℕ)
    (hd : IsDescartesNumber n) (hcf : Powerfree 3 n) (hcard : n.primeFactors.card < 7) :
    n = descartesExample := by
  sorry

/-- Is $198{,}585{,}576{,}189$ the only Descartes number? -/
@[category research open, question, AMS 11]
theorem descartes_number_unique :
    ∀ n : ℕ, IsDescartesNumber n → n = descartesExample := by
  sorry

end DescartesNumber
