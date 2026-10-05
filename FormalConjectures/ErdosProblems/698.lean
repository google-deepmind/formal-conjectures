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
# Erdős Problem 698

*References:*
- [erdosproblems.com/698](https://www.erdosproblems.com/698)
- [ErSz78] Erdős, P. and Szekeres, G., *Some number theoretic problems on binomial
  coefficients*. Austral. Math. Soc. Gaz. (1978), 97-99.
- [Be11] Bergman, George M., *On common divisors of multinomial coefficients*. Bull. Aust.
  Math. Soc. (2011), 138--157.
-/

@[expose] public section

namespace Erdos698

open Filter

/--
Is there some $h(n)\to \infty$ such that for all $2\leq i<j\leq n/2$
$$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \geq h(n)?$$

This was resolved by Bergman [Be11], who proved that for any $2\leq i<j\leq n/2$
$$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \gg n^{1/2}\frac{2^i}{i^{3/2}},$$
where the implied constant is absolute.

The linked formal proof (van Doorn and Aristotle, see `erdos_698.variants.bergman`) gives the
explicit bound $\gcd > \frac{2^i \sqrt n}{4 i \sqrt{i - 1}}$, so $h(n) = \lfloor \sqrt n / 4 \rfloor$
works since $i \sqrt{i - 1} \le 2^i$ for $i \ge 2$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos698.lean#L452"]
theorem erdos_698 : answer(True) ↔
    ∃ h : ℕ → ℕ, Tendsto h atTop atTop ∧
      ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
        h n ≤ Nat.gcd (n.choose i) (n.choose j) := by
  sorry

/--
A problem of Erdős and Szekeres, who observed that
$$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \geq \frac{\binom{n}{i}}{\binom{j}{i}}
\geq 2^i$$
(in particular the greatest common divisor is always $>1$).
-/
@[category research solved, AMS 5 11]
theorem erdos_698.variants.erdos_szekeres (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ n / 2) :
    (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) := by
  have _ := hi -- the argument does not need `1 ≤ i`
  have hjn : 2 * j ≤ n := by omega
  have hcpos : 0 < j.choose i := Nat.choose_pos hij.le
  have hcR : (0 : ℝ) < (j.choose i : ℝ) := by exact_mod_cast hcpos
  -- the identity `choose n j * choose j i = choose n i * choose (n - i) (j - i)`
  have hid : n.choose j * j.choose i = n.choose i * (n - i).choose (j - i) :=
    Nat.choose_mul hij.le
  -- `choose n i` divides `gcd (choose n i) (choose n j) * choose j i`
  have hdvd : n.choose i ∣ Nat.gcd (n.choose i) (n.choose j) * j.choose i := by
    rw [← Nat.gcd_mul_right]
    exact Nat.dvd_gcd (dvd_mul_right _ _) (by rw [hid]; exact dvd_mul_right _ _)
  have hgpos : 0 < Nat.gcd (n.choose i) (n.choose j) :=
    Nat.gcd_pos_of_pos_left _ (Nat.choose_pos (by omega))
  have hle : n.choose i ≤ Nat.gcd (n.choose i) (n.choose j) * j.choose i :=
    Nat.le_of_dvd (Nat.mul_pos hgpos hcpos) hdvd
  -- growth: `2 ^ k * choose j k ≤ choose n k` for `k ≤ j`
  have hgrow : ∀ k : ℕ, k ≤ j → 2 ^ k * j.choose k ≤ n.choose k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) :=
        Nat.choose_succ_right_eq n k
      have h2 : j.choose (k + 1) * (k + 1) = j.choose k * (j - k) :=
        Nat.choose_succ_right_eq j k
      have h3 : 2 * (j - k) ≤ n - k := by omega
      have h4 : 2 ^ (k + 1) * j.choose (k + 1) * (k + 1) ≤ n.choose (k + 1) * (k + 1) := by
        calc 2 ^ (k + 1) * j.choose (k + 1) * (k + 1)
            = 2 ^ k * j.choose k * (2 * (j - k)) := by
              rw [mul_assoc, h2]; ring
          _ ≤ n.choose k * (n - k) := Nat.mul_le_mul ih' h3
          _ = n.choose (k + 1) * (k + 1) := h1.symm
      exact Nat.le_of_mul_le_mul_right h4 (Nat.succ_pos k)
  constructor
  · rw [div_le_iff₀ hcR]
    exact_mod_cast hle
  · rw [le_div_iff₀ hcR]
    exact_mod_cast hgrow i hij.le

/--
This inequality is sharp for $i=1$, $j=p$, and $n=2p$.
-/
@[category research solved, AMS 5 11]
theorem erdos_698.variants.erdos_szekeres_sharp (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (Nat.gcd ((2 * p).choose 1) ((2 * p).choose p) : ℝ) =
        ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) ∧
      ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) = (2 : ℝ) ^ 1 := by
  have := Fact.mk hp
  have hp0 : 0 < p := hp.pos
  -- `choose (2p) p ≡ 2 (mod p)` by Lucas' theorem
  have hlucas : (2 * p).choose p ≡ 2 [MOD p] := by
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := 2 * p) (k := p)
    have e1 : 2 * p % p = 0 := by simp
    have e2 : p % p = 0 := by simp
    have e3 : 2 * p / p = 2 := Nat.mul_div_cancel _ hp0
    have e4 : p / p = 1 := Nat.div_self hp0
    simpa [e1, e2, e3, e4, Nat.choose_one_right] using h
  have hpnd : ¬ p ∣ (2 * p).choose p := by
    intro hd
    have h0 : (2 * p).choose p ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 hd
    have h2 : 2 ≡ 0 [MOD p] := hlucas.symm.trans h0
    have : p ∣ 2 := (Nat.modEq_zero_iff_dvd).1 h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hev : 2 ∣ (2 * p).choose p := by
    have := Nat.two_dvd_centralBinom_of_one_le hp0
    simpa [Nat.centralBinom, two_mul] using this
  have hg : Nat.gcd ((2 * p).choose 1) ((2 * p).choose p) = 2 := by
    rw [Nat.choose_one_right]
    apply Nat.dvd_antisymm
    · have hg1 : Nat.gcd (2 * p) ((2 * p).choose p) ∣ 2 * p := Nat.gcd_dvd_left _ _
      have hcop : Nat.Coprime (Nat.gcd (2 * p) ((2 * p).choose p)) p := by
        apply Nat.Coprime.symm
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        exact hpnd (hd.trans (Nat.gcd_dvd_right _ _))
      exact hcop.dvd_of_dvd_mul_right hg1
    · exact Nat.dvd_gcd (Dvd.intro _ rfl) hev
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
  rw [hg]
  simp only [Nat.choose_one_right]
  push_cast
  refine ⟨?_, ?_⟩
  · field_simp
  · field_simp

/--
This was resolved by Bergman [Be11], who proved that for any $2\leq i<j\leq n/2$
$$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \gg n^{1/2}\frac{2^i}{i^{3/2}},$$
where the implied constant is absolute.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos698.lean"]
theorem erdos_698.variants.bergman :
    ∃ c : ℝ, 0 < c ∧ ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
      c * (Real.sqrt (n : ℝ) * (2 : ℝ) ^ i / ((i : ℝ) * Real.sqrt (i : ℝ))) ≤
        (Nat.gcd (n.choose i) (n.choose j) : ℝ) := by
  sorry

end Erdos698
