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
# Heath-Brown's Conjecture and Bounds on Linnik's Constant

Given coprime integers $1 \le a < d$ with $d \ge 2$, write $p(a, d)$ for the minimal prime
satisfying $p \equiv a \pmod d$. Yuri V. Linnik (1944) proved that universal constants $C, L > 0$
satisfy $p(a, d) \le C d^L$; the infimum of admissible exponents $L$ is *Linnik's constant*.
Unconditionally, Triantafyllos Xylouris (2011) established $L \le 5$, whereas assuming GRH
yields $p(a, d) \le \varphi(d)^2 (\log d)^2$ (hence $L \le 2$). D. R. Heath-Brown
(1992) conjectured the strict unconditional bound $p(a, d) < d^2$.

*References:*
- [Wikipedia: Linnik's theorem](https://en.wikipedia.org/wiki/Linnik%27s_theorem)
- [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#Prime_numbers)
- Yu. V. Linnik, *On the least prime in an arithmetic progression. I. The basic theorem*,
  Mat. Sbornik **15(57)** (1944), no. 2, 139–178.
- D. R. Heath-Brown, *Zero-free regions for Dirichlet $L$-functions, and the least prime in an
  arithmetic progression*, Proc. London Math. Soc. (3) **64** (1992), no. 2, 265–338,
  https://doi.org/10.1112/plms/s3-64.2.265
- T. Xylouris, *On Linnik's constant*, Acta Arith. **150** (2011), no. 1, 65–91,
  https://doi.org/10.4064/aa150-1-4; *Über die Nullstellen der Dirichletschen $L$-Funktionen und
  die kleinste Primzahl in einer arithmetischen Progression*, Bonner Mathematische Schriften
  **404**, Universität Bonn, 2011.
-/

@[expose] public section

namespace LinnikConstantConjecture

/-- Minimal prime $p$ satisfying $p \equiv a \pmod d$ (evaluating to $0$ when none exists). -/
noncomputable def leastPrimeInAP (a d : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ p ≡ a [MOD d]}

/-- By Dirichlet's theorem, whenever $d \ne 0$ and $\gcd(a, d) = 1$, `leastPrimeInAP a d` is prime
and congruent to $a$ modulo $d$. -/
@[category API, AMS 11]
theorem leastPrimeInAP_prime_and_modEq {a d : ℕ} (hd : d ≠ 0) (hcop : a.Coprime d) :
    (leastPrimeInAP a d).Prime ∧ leastPrimeInAP a d ≡ a [MOD d] := by
  unfold leastPrimeInAP
  obtain ⟨p, _, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq 0 hd hcop
  exact Nat.sInf_mem (s := {p : ℕ | p.Prime ∧ p ≡ a [MOD d]}) ⟨p, hp, hmod⟩

/-- Modulo $4$ witnesses: `leastPrimeInAP 3 4 = 3` and `leastPrimeInAP 1 4 = 5`. -/
@[category test, AMS 11]
theorem leastPrimeInAP_mod_four :
    leastPrimeInAP 3 4 = 3 ∧ leastPrimeInAP 1 4 = 5 := by
  refine ⟨?_, ?_⟩
  · have hle : leastPrimeInAP 3 4 ≤ 3 := Nat.sInf_le ⟨by norm_num, rfl⟩
    obtain ⟨hp, hmod⟩ := leastPrimeInAP_prime_and_modEq (a := 3) (d := 4) (by omega) (by decide)
    have hge := hp.two_le
    interval_cases leastPrimeInAP 3 4
    · rw [Nat.ModEq] at hmod; omega
    · rfl
  · have hle : leastPrimeInAP 1 4 ≤ 5 := Nat.sInf_le ⟨by norm_num, rfl⟩
    obtain ⟨hp, hmod⟩ := leastPrimeInAP_prime_and_modEq (a := 1) (d := 4) (by omega) (by decide)
    have hge := hp.two_le
    interval_cases leastPrimeInAP 1 4
    · rw [Nat.ModEq] at hmod; omega
    · rw [Nat.ModEq] at hmod; omega
    · norm_num at hp
    · rfl

/-- Degenerate non-coprime case ($a = 0, d = 4$): no multiple of $4$ is prime, so
`leastPrimeInAP 0 4 = 0`. -/
@[category test, AMS 11]
theorem not_prime_leastPrimeInAP_zero_four :
    leastPrimeInAP 0 4 = 0 ∧ ¬ (leastPrimeInAP 0 4).Prime := by
  have hempty : {p : ℕ | p.Prime ∧ p ≡ 0 [MOD 4]} = ∅ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hmod
    have h4 : 4 ∣ p := Nat.dvd_of_mod_eq_zero hmod
    rcases hp.eq_one_or_self_of_dvd 4 h4 with h | h
    · omega
    · subst h; norm_num at hp
  have h0 : leastPrimeInAP 0 4 = 0 := by
    unfold leastPrimeInAP
    rw [hempty, Nat.sInf_empty]
  exact ⟨h0, by rw [h0]; exact Nat.not_prime_zero⟩

/--
**Heath-Brown's Conjecture** (1992): for all integers $d \ge 2$ and $1 \le a < d$ with
$\gcd(a, d) = 1$, the minimal prime $p(a, d) \equiv a \pmod d$ satisfies $p(a, d) < d^2$.
-/
@[category research open, AMS 11]
theorem linnik_least_prime_lt_sq :
    ∀ a d : ℕ, 2 ≤ d → 1 ≤ a → a < d → a.Coprime d →
      leastPrimeInAP a d < d ^ 2 := by
  sorry

/--
Unconditional $L \le 2$ bound on Linnik's constant: for each $\varepsilon > 0$, some $C > 0$
satisfies $p(a, d) \le C d^{2 + \varepsilon}$ whenever $d \ge 2$ and $\gcd(a, d) = 1$.
-/
@[category research open, AMS 11]
theorem linnik_least_prime_lt_sq.variants.constant_le_two :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ a d : ℕ, 2 ≤ d → a.Coprime d →
          (leastPrimeInAP a d : ℝ) ≤ C * (d : ℝ) ^ (2 + ε) := by
  sorry

/--
**Linnik's Theorem** (1944): there exist constants $C, L > 0$ with $p(a, d) \le C d^L$ whenever
$d \ge 2$ and $\gcd(a, d) = 1$.
-/
@[category research solved, AMS 11]
theorem linnik_theorem :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ a d : ℕ, 2 ≤ d → a.Coprime d →
        (leastPrimeInAP a d : ℝ) ≤ C * (d : ℝ) ^ L := by
  sorry

/--
**Xylouris' Bound** (2011): there exists $C > 0$ with $p(a, d) \le C d^5$ whenever $d \ge 2$ and
$\gcd(a, d) = 1$.
-/
@[category research solved, AMS 11]
theorem linnik_theorem.variants.xylouris_five :
    ∃ C : ℝ, 0 < C ∧
      ∀ a d : ℕ, 2 ≤ d → a.Coprime d →
        (leastPrimeInAP a d : ℝ) ≤ C * (d : ℝ) ^ (5 : ℝ) := by
  sorry

end LinnikConstantConjecture
