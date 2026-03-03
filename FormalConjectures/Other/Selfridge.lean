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

import FormalConjectures.Util.ProblemImports

/-!
# Selfridge's conjectures

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/John_Selfridge#Selfridge's_conjecture_about_primality_testing)
-/

namespace Selfridge

section PrimalityTesting

/-- A number `p` satisfies the *Selfridge condition* if
1. `p` is odd,
2. `p ≡ ± 2 (mod 5)`,
3. `2^(p-1) ≡ 1 (mod p)`
4. `(p+1).fib ≡ 0 (mod p)`


This is the condition that is tested in the PSW conjecture.
Note: this is non-standard terminology. -/
@[mk_iff]
structure IsSelfridge (p : ℕ) where
  is_odd : Odd p
  mod_5 : p ≡ 2 [MOD 5] ∨ p ≡ 3 [MOD 5]
  pow_2 : 2^(p-1) ≡ 1 [MOD p]
  fib : (p+1).fib ≡ 0 [MOD p]

/-- A number `p` satisfies the *Pseudo Selfridge condition* if
1. `p` is odd,
2. `p ≡ ± 1 (mod 5)`,
3. `2^(p-1) ≡ 1 (mod p)`
4. `(p-1).fib ≡ 0 (mod p)`


This is a variant of the condition that is tested in the PSW conjecture, and appears in the
wiki page mentioned above.

Note: this is non-standard terminology. -/
@[mk_iff]
structure IsPseudoSelfridge (p : ℕ) where
  is_odd : Odd p
  mod_5 : p ≡ 1 [MOD 5] ∨ p ≡ 4 [MOD 5]
  pow_2 : 2^(p-1) ≡ 1 [MOD p]
  fib : (p-1).fib ≡ 0 [MOD p]

/--
**PSW conjecture** (Selfridge's test)
Let $p$ be an odd number, with $p \equiv \pm 2 \pmod{5}$, $2^{p-1} \equiv 1 \pmod{p}$
and $F_{p+1} \equiv 0 \pmod{p}$, then $p$ is a prime number.
-/
@[category research open, AMS 11]
theorem selfridge_conjecture (p : ℕ) (hp : IsSelfridge p) : p.Prime := by
  sorry

/-! ### Proof infrastructure for pseudo-counterexamples -/

set_option maxHeartbeats 400000000
set_option maxRecDepth 100000

private def modPowAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, res => res
  | fuel + 1, b, e, res =>
    if e = 0 then res
    else if e % 2 = 1 then modPowAux m fuel ((b * b) % m) (e / 2) ((res * b) % m)
    else modPowAux m fuel ((b * b) % m) (e / 2) res

private def modPow (base exp m : ℕ) : ℕ :=
  if m = 1 then 0 else modPowAux m 100 (base % m) exp 1

private lemma modPowAux_spec (m fuel b e res : ℕ) (h_fuel : e < 2 ^ fuel) :
    (modPowAux m fuel b e res : ZMod m) = (res : ZMod m) * (b : ZMod m) ^ e := by
  induction fuel generalizing b e res with
  | zero => simp [Nat.lt_one_iff.mp h_fuel, modPowAux]
  | succ fuel ih =>
    rw [modPowAux]; split_ifs with h_e h_odd
    · rw [h_e, pow_zero, mul_one]
    · rw [ih _ _ _ (by omega)]
      have he : e = 2 * (e / 2) + 1 := by omega
      rw [ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul]
      nth_rw 2 [he]; rw [pow_add, pow_one, pow_mul]; ring
    · rw [ih _ _ _ (by omega)]
      have he : e = 2 * (e / 2) := by omega
      rw [ZMod.natCast_mod, Nat.cast_mul]; nth_rw 2 [he]; rw [pow_mul]; ring

private lemma pow2_modEq_of_modPow {e m : ℕ} (hm : 1 < m) (he : e < 2 ^ 100)
    (h : modPow 2 e m = 1 % m) : 2 ^ e ≡ 1 [MOD m] := by
  have hspec := modPowAux_spec m 100 (2 % m) e 1 he
  simp only [Nat.cast_one, one_mul, ZMod.natCast_mod] at hspec
  simp only [modPow, show ¬m = 1 from by omega, ↓reduceIte, Nat.mod_eq_of_lt hm] at h
  have haux : (modPowAux m 100 (2 % m) e 1 : ZMod m) = 1 := by
    have := congr_arg (Nat.cast : ℕ → ZMod m) h; simpa using this
  have hzmod : ((2 : ℕ) : ZMod m) ^ e = 1 := hspec ▸ haux
  exact_mod_cast (ZMod.natCast_eq_natCast_iff (2 ^ e) 1 m).mp (by push_cast; exact hzmod)

private lemma fib_le_succ (k : ℕ) : Nat.fib k ≤ Nat.fib (k + 1) := by
  induction k with
  | zero => simp [Nat.fib]
  | succ n ih => rw [Nat.fib_add_two]; omega

private lemma fib_two_mul_sub (k : ℕ) :
    Nat.fib (2 * k) + Nat.fib k ^ 2 = 2 * Nat.fib k * Nat.fib (k + 1) := by
  have h := Nat.fib_two_mul k
  nlinarith [fib_le_succ k,
             Nat.sub_add_cancel (by linarith [fib_le_succ k] : Nat.fib k ≤ 2 * Nat.fib (k + 1))]

private lemma fib_even_ZMod (m : ℕ) [NeZero m] (k : ℕ) :
    (Nat.fib (2 * k) : ZMod m) =
    (Nat.fib k : ZMod m) * (2 * (Nat.fib (k + 1) : ZMod m) - (Nat.fib k : ZMod m)) := by
  have := congr_arg (Nat.cast : ℕ → ZMod m) (fib_two_mul_sub k)
  push_cast at this; linear_combination this - (Nat.fib k : ZMod m) ^ 2

private lemma fib_odd_ZMod (m : ℕ) [NeZero m] (k : ℕ) :
    (Nat.fib (2 * k + 1) : ZMod m) =
    (Nat.fib k : ZMod m) ^ 2 + (Nat.fib (k + 1) : ZMod m) ^ 2 := by
  have := congr_arg (Nat.cast : ℕ → ZMod m) (Nat.fib_two_mul_add_one k)
  push_cast at this ⊢; linear_combination this

private def fibZMod (m : ℕ) [NeZero m] : ℕ → ℕ → ZMod m × ZMod m
  | 0, _ => (0, 1)
  | _, 0 => (0, 1)
  | fuel + 1, n + 1 =>
    let ⟨a, b⟩ := fibZMod m fuel ((n + 1) / 2)
    let c := a * (2 * b - a)
    let d := a ^ 2 + b ^ 2
    if (n + 1) % 2 == 1 then (d, c + d) else (c, d)

private lemma fibZMod_correct (m : ℕ) [NeZero m] (fuel n : ℕ) (hf : n < 2 ^ fuel) :
    fibZMod m fuel n = ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m)) := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := Nat.lt_one_iff.mp hf
    subst hn; simp [fibZMod, Nat.fib]
  | succ fuel ih =>
    cases n with
    | zero => simp [fibZMod, Nat.fib]
    | succ n =>
      have hd : (n + 1) / 2 < 2 ^ fuel := by
        have : n + 1 < 2 * 2 ^ fuel := by simp only [pow_succ] at hf; linarith
        omega
      set k := (n + 1) / 2
      rw [show fibZMod m (fuel + 1) (n + 1) =
              (let ⟨a, b⟩ := fibZMod m fuel k
               let c := a * (2 * b - a); let d := a ^ 2 + b ^ 2
               if (n + 1) % 2 == 1 then (d, c + d) else (c, d)) from rfl,
          ih k hd]
      simp only
      have hfc : (Nat.fib k : ZMod m) * (2 * (Nat.fib (k + 1) : ZMod m) - (Nat.fib k : ZMod m)) =
                 (Nat.fib (2 * k) : ZMod m) := (fib_even_ZMod m k).symm
      have hfd : (Nat.fib k : ZMod m) ^ 2 + (Nat.fib (k + 1) : ZMod m) ^ 2 =
                 (Nat.fib (2 * k + 1) : ZMod m) := (fib_odd_ZMod m k).symm
      by_cases hmod : (n + 1) % 2 == 1
      · have hn2k1 : n + 1 = 2 * k + 1 := by simp only [beq_iff_eq] at hmod; omega
        simp only [hmod, ↓reduceIte, hfd, hfc]
        apply Prod.ext
        · rw [← hn2k1]
        · push_cast [show n + 2 = 2 * k + 2 from by omega,
                     show 2 * k + 2 = (2 * k + 1) + 1 from by ring,
                     Nat.fib_add_two, ← fib_even_ZMod m k, ← fib_odd_ZMod m k]; ring
      · have hn2k : n + 1 = 2 * k := by
          simp only [Bool.not_eq_true, beq_eq_false_iff_ne, ne_eq] at hmod; omega
        simp only [Bool.not_eq_true] at hmod
        simp only [hmod, Bool.false_eq_true, ↓reduceIte, hfc, hfd]
        apply Prod.ext
        · rw [← hn2k]
        · simp [show n + 2 = 2 * k + 1 from by omega, hfd]

private lemma fibZMod_fst_modEq (m n fuel : ℕ) [NeZero m]
    (hf : n < 2 ^ fuel)
    (h : (fibZMod m fuel n).1 = 0) : Nat.fib n ≡ 0 [MOD m] := by
  have hcor := fibZMod_correct m fuel n hf
  simp only [hcor] at h
  rw [Nat.ModEq, Nat.zero_mod]
  exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff (Nat.fib n) m).mp h)

private instance : NeZero 6601 := ⟨by norm_num⟩
private instance : NeZero 30889 := ⟨by norm_num⟩

private lemma is_odd_6601    : Odd 6601              := by norm_num [Nat.odd_iff]
private lemma not_prime_6601 : ¬(6601).Prime         := by norm_num [show 6601 = 7 * 23 * 41 from by norm_num]
private lemma mod5_1_6601    : 6601 ≡ 1 [MOD 5]      := by norm_num [Nat.ModEq]

private lemma is_odd_30889    : Odd 30889             := by norm_num [Nat.odd_iff]
private lemma not_prime_30889 : ¬(30889).Prime        := by norm_num [show 30889 = 17 * 23 * 79 from by norm_num]
private lemma mod5_4_30889    : 30889 ≡ 4 [MOD 5]     := by norm_num [Nat.ModEq]

private lemma modpow_6601   : modPow 2 6600 6601   = 1 % 6601   := by decide
private lemma modpow_30889  : modPow 2 30888 30889 = 1 % 30889  := by decide

private lemma fibzmod_6601  : (fibZMod 6601 20 6600).1  = 0 := by decide
private lemma fibzmod_30889 : (fibZMod 30889 20 30888).1 = 0 := by decide

private lemma pow2_6600_modeq : 2 ^ 6600 ≡ 1 [MOD 6601] :=
  pow2_modEq_of_modPow (by norm_num) (by norm_num) modpow_6601

private lemma pow2_30888_modeq : 2 ^ 30888 ≡ 1 [MOD 30889] :=
  pow2_modEq_of_modPow (by norm_num) (by norm_num) modpow_30889

private lemma fib_6600_modeq : Nat.fib 6600 ≡ 0 [MOD 6601] :=
  fibZMod_fst_modEq 6601 6600 20 (by norm_num) fibzmod_6601

private lemma fib_30888_modeq : Nat.fib 30888 ≡ 0 [MOD 30889] :=
  fibZMod_fst_modEq 30889 30888 20 (by norm_num) fibzmod_30889

/--
Selfridge's test variant:
Let $p$ be an odd number, with $p \equiv \pm 1 \pmod{5}$, $2^{p-1} \equiv 1 \pmod{p}$
and $F_{p-1} \equiv 0 \pmod{p}$, then $p$ is a prime number.

This test does not work.
-/
@[category undergraduate, AMS 11]
theorem selfridge_conjecture.variants.exist_pseudo_counterexample :
    ∃ n : ℕ, IsPseudoSelfridge n ∧ ¬ n.Prime :=
  ⟨6601, ⟨is_odd_6601, Or.inl mod5_1_6601, pow2_6600_modeq, fib_6600_modeq⟩, not_prime_6601⟩

/--
Selfridge's test variant:
Let $p$ be an odd number, with $p \equiv \pm 1 \pmod{5}$, $2^{p-1} \equiv 1 \pmod{p}$
and $F_{p-1} \equiv 0 \pmod{p}$, then $p$ is a prime number.

The number $6601$ is a conterexample to this test satisfying $6601 ≡ 1 \mod 5$
-/
@[category high_school, AMS 11]
theorem selfridge_conjecture.variants.pseudo_counterexample :
    IsPseudoSelfridge 6601 ∧ ¬ (6601).Prime ∧ 6601 ≡ 1 [MOD 5] :=
  ⟨⟨is_odd_6601, Or.inl mod5_1_6601, pow2_6600_modeq, fib_6600_modeq⟩,
   not_prime_6601, mod5_1_6601⟩

/--
Selfridge's test variant:
Let $p$ be an odd number, with $p \equiv \pm 1 \pmod{5}$, $2^{p-1} \equiv 1 \pmod{p}$
and $F_{p-1} \equiv 0 \pmod{p}$, then $p$ is a prime number.

The number $30889$ is a conterexample to this test satisfying $30889 ≡ - 1 \mod 5$
-/
@[category high_school, AMS 11]
theorem selfridge_conjecture.variants.pseudo_counterexample' :
    IsPseudoSelfridge 30889 ∧ ¬ (30889).Prime ∧ 30889 ≡ 4 [MOD 5] :=
  ⟨⟨is_odd_30889, Or.inr mod5_4_30889, pow2_30888_modeq, fib_30888_modeq⟩,
   not_prime_30889, mod5_4_30889⟩

end PrimalityTesting

section FermatNumbers

/-!
# Selfridge's conjectures about Fermat numbers
-/

/--
**OEIS A46052**
The number of distinct prime factors of nth Fermat number.
Known terms: 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 5
-/
def fermatFactors (n : ℕ) : ℕ := n.fermatNumber.primeFactors.card

/--
Selfridge conjectured that the number of prime factors of the `n`-th Fermat number does not grow
monotonically in $n$.
-/
@[category research open, AMS 11]
theorem selfridge_seq_conjecture : ¬ Monotone fermatFactors := by
  sorry

/--
Selfridge conjectured that the number of prime factors of the `n`-th Fermat number does not grow
monotonically in $n$.

A sufficient condition for this conjecture to hold is that there exists a Fermat prime larger than
65537.
-/
@[category research solved, AMS 11]
theorem selfridge_seq_conjecture.variants.sufficient_condition (n : ℕ) (hn : Prime n.fermatNumber)
    (hn' : n ≥ 5) : type_of% selfridge_seq_conjecture := by
  sorry

end FermatNumbers

end Selfridge
