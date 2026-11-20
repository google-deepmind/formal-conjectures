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
# Erdős Problem 282

*Reference:* [erdosproblems.com/282](https://www.erdosproblems.com/282)
-/

@[expose] public section

open Filter Real

namespace Erdos282

/-- Let $A\subseteq \mathbb{N}$ be an infinite set and consider the following
greedy algorithm for a rational $x$: choose the minimal $n\in A$ not used so far such
that $n\geq 1/x$ and repeat with $x$ replaced by $x-\frac{1}{n}$.

This process of subtracting unit fractions is modelled in `greedyUnitFractionRem`.
At each step `t : ℕ`, the function `greedyUnitFractionRem A x t` returns the remainder
of `x` with respect to the first `t + 1` unit fractions, with distinct denominators taken
from `A`. Once the remainder reaches `0` it stays `0`, and the process terminates. This
corresponds to producing a representation of `x` as the sum of distinct unit fractions with
denominators from `A`, however this function does not return this representation. -/
noncomputable def greedyUnitFractionRem (A : Set ℕ) (x : ℚ) (t : ℕ) : ℚ :=
  if x ≤ 0 then 0 else
    let n := sInf { n | n ∈ A ∧ 1 / x ≤ n }
    let rem := x - 1 / n
    match t with
    | 0 => rem
    | t + 1 => greedyUnitFractionRem (A \ {n}) rem t

@[category test, AMS 5]
theorem greedyUnitFractionRem_zero (n : ℕ) : greedyUnitFractionRem .univ (1 / n) 0 = 0 := by
  simp [greedyUnitFractionRem, Set.Ici_def]

@[category test, AMS 5]
theorem greedyUnitFractionRem_one (n : ℕ) : greedyUnitFractionRem .univ (1 / n) 1 = 0 := by
  simp [greedyUnitFractionRem, Set.Ici_def]

/-- Let $A\subseteq \mathbb{N}$ be an infinite set and consider the following
greedy algorithm for a rational $x\in (0,1)$: choose the minimal $n\in A$ not used
so far such that $n\geq 1/x$ and repeat with $x$ replaced by $x-\frac{1}{n}$. If this
terminates after finitely many steps then this produces a representation of
$x$ as the sum of distinct unit fractions with denominators from $A$.

Does this process always terminate if $x$ has odd denominator and $A$ is the
set of odd numbers? -/
@[category research open, AMS 5]
theorem erdos_282 {x : ℚ} (hx : x ∈ Set.Ioo 0 1) (hx_den : Odd x.den) :
    greedyUnitFractionRem { n | Odd n } x =ᶠ[atTop] 0 := by
  sorry

def erdos_282.variants.general.answer : Set (ℚ × Set ℕ) := sorry

/-- More generally, for which pairs $x$ and $A$ does this process terminate? -/
@[category research open, question value, AMS 5]
theorem erdos_282.variants.general (x : ℚ) (A : Set ℕ) :
      greedyUnitFractionRem A x =ᶠ[atTop] 0 ↔ (x, A) ∈ erdos_282.variants.general.answer := by
  sorry

/-- In 1202 Fibonacci observed that this process terminates for any $x$ when $A=\mathbb{N}$. -/
@[category textbook, AMS 5]
theorem erdos_282.variants.fibonacci {x : ℚ} (hx : x ∈ Set.Ioo 0 1) :
    greedyUnitFractionRem .univ x =ᶠ[atTop] 0 := by
  sorry

section GrahamCounterexample

/-- `A` consists of integers `≡ 1 (mod 3)` and contains every such integer above `3 * q`. -/
private def ValidSet (A : Set ℕ) (q : ℕ) : Prop :=
  1 ≤ q ∧ ∀ k, (k ∈ A → k % 3 = 1) ∧ (3 * q < k → k % 3 = 1 → k ∈ A)

/-- Remainder of the shape `m / (3 * m * q - 1)` arising along the `6`-step cycle. -/
private noncomputable def sFrac (m q : ℕ) : ℚ := (m : ℚ) / (3 * m * q - 1)

/-- One greedy step from `sFrac m q` selects `3 * q + 1` and transitions to `sFrac m' q'`. -/
@[category API, AMS 5]
private lemma greedy_step (m m' : ℕ) {A : Set ℕ} {q q' : ℕ} (hA : ValidSet A q) (hlt : q < q')
    (hrel : ((m : ℚ) + 1) * (3 * m' * q' - 1) = m' * (3 * m * q - 1) * (3 * q + 1))
    (hm : 1 ≤ m := by decide) (hm' : 1 ≤ m' := by decide) :
    ValidSet (A \ {3 * q + 1}) q' ∧
      greedyUnitFractionRem A (sFrac m q) 0 = sFrac m' q' ∧
      ∀ t, greedyUnitFractionRem A (sFrac m q) (t + 1) =
        greedyUnitFractionRem (A \ {3 * q + 1}) (sFrac m' q') t := by
  have hden {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : (0 : ℚ) < 3 * a * b - 1 := by
    nlinarith [show (1 : ℚ) ≤ a from mod_cast ha, show (1 : ℚ) ≤ b from mod_cast hb]
  have hd := hden hm hA.1
  have hx : 0 < sFrac m q := div_pos (by positivity) hd
  have hs : sInf { k : ℕ | k ∈ A ∧ 1 / sFrac m q ≤ k } = 3 * q + 1 :=
    IsLeast.csInf_eq ⟨⟨(hA.2 _).2 (by omega) (by omega), by
      rw [sFrac, one_div_div, div_le_iff₀ (by positivity)]
      push_cast
      linarith [show (1 : ℚ) ≤ m from mod_cast hm]⟩, fun k ⟨hkA, hle⟩ ↦ by
      rw [sFrac, one_div_div, div_le_iff₀ (by positivity)] at hle
      have : 3 * m * q ≤ k * m + 1 := mod_cast (by linarith : (3 * m * q : ℚ) ≤ k * m + 1)
      by_contra!
      nlinarith [Nat.mul_le_mul_right m (show k + 2 ≤ 3 * q by have := (hA.2 k).1 hkA; omega)]⟩
  have hsub : sFrac m q - 1 / (3 * q + 1 : ℕ) = sFrac m' q' := by
    simp only [sFrac, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [div_sub_div _ _ hd.ne' (by positivity), div_eq_div_iff
      (mul_ne_zero hd.ne' (by positivity)) (hden hm' (by have := hA.1; omega)).ne']
    linarith
  refine ⟨⟨by have := hA.1; omega, fun k ↦ ⟨fun hk ↦ (hA.2 k).1 hk.1,
    fun hk hmod ↦ ⟨(hA.2 k).2 (by omega) hmod, by simp; omega⟩⟩⟩, ?_, fun _ ↦ ?_⟩ <;>
    (rw [greedyUnitFractionRem, if_neg (not_le.mpr hx)]; dsimp only; rw [hs, hsub])

/-- Every `6` greedy steps preserve the congruence invariant on `c`, keeping the remainder `> 0`. -/
@[category API, AMS 5]
private lemma pos_at_six_mul (K : ℕ) {A : Set ℕ} {c : ℕ} (hA : ValidSet A (2 * c))
    (hc7 : c % 7 = 6) (hc5 : c % 5 = 0 ∨ c % 25 = 18) :
    0 < greedyUnitFractionRem A (sFrac 1 (2 * c)) (6 * K) := by
  induction K generalizing A c with
  | zero =>
    have hc1 : 1 ≤ c := by have := hA.1; omega
    rw [(greedy_step 1 2 hA (q' := 6 * c ^ 2) (by nlinarith) (by push_cast; ring)).2.1]
    exact div_pos zero_lt_two (by push_cast; nlinarith [show (1 : ℚ) ≤ c from mod_cast hc1])
  | succ K ih =>
    have hc1 : 1 ≤ c := by have := hA.1; omega
    generalize hu2 : c ^ 2 * (36 * c ^ 2 + 1) = u2
    generalize hq3 : u2 * (9 * u2 + 1) = q3
    have hq3_2 : q3 % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one u2 with h | h <;>
        simp [← hq3, Nat.mul_mod, Nat.add_mod, h]
    have hq3_25 : q3 % 25 = 0 ∨ q3 % 25 = 10 := by
      rcases hc5 with h | h
      · obtain ⟨r, rfl⟩ := Nat.dvd_of_mod_eq_zero h
        exact Or.inl (by simp [← hq3, ← hu2, show (5 * r) ^ 2 = 25 * r ^ 2 by ring, Nat.mul_mod])
      · exact Or.inr (by simp [← hq3, ← hu2, Nat.mul_mod, Nat.add_mod, Nat.pow_mod, h])
    obtain ⟨v3, hv3⟩ : 10 ∣ q3 := Nat.dvd_of_mod_eq_zero (by clear * - hq3_2 hq3_25; omega)
    generalize hu4 : v3 * (40 * v3 + 1) = u4
    generalize hk5 : u4 * (45 * u4 + 2) = k5
    have hq3_7 : q3 % 7 = 3 := by
      simp [← hq3, ← hu2, Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hc7]
    have hk5_7 : k5 % 7 = 1 := by
      have hv3_7 : v3 % 7 = 1 := by clear * - hv3 hq3_7; omega
      simp [← hk5, ← hu4, Nat.mul_mod, Nat.add_mod, hv3_7]
    generalize ht : k5 / 7 = t
    generalize hc' : 7 * (36 * t ^ 2 + 11 * t) + 6 = c'
    have h7c' : 7 * c' = 36 * k5 ^ 2 + 5 * k5 + 1 := by
      rw [← hc', show k5 = 7 * t + 1 by clear * - hk5_7 ht; omega]
      ring
    have hc'5 : c' % 5 = 0 ∨ c' % 25 = 18 := by
      rcases (show v3 % 5 = 0 ∨ v3 % 5 = 1 by clear * - hv3 hq3_25; omega) with h | h
      · obtain ⟨r, hr⟩ : 5 ∣ k5 :=
          Nat.dvd_of_mod_eq_zero (by simp [← hk5, ← hu4, Nat.mul_mod, h])
        have hm : 7 * c' = 25 * (36 * r ^ 2 + r) + 1 := by rw [h7c', hr]; ring
        exact Or.inr (by clear * - hm; omega)
      · have hm : (7 * c') % 5 = 0 := by
          simp [h7c', ← hk5, ← hu4, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h]
        exact Or.inl (by clear * - hm; omega)
    obtain ⟨hA1, -, hs0⟩ := greedy_step 1 2 hA (q' := 6 * c ^ 2)
      (by clear * - hc1; nlinarith) (by push_cast; ring)
    obtain ⟨hA2, -, hs1⟩ := greedy_step 2 3 hA1 (q' := 2 * u2)
      (by
        clear * - hu2 hc1
        nlinarith [Nat.mul_le_mul_right (36 * c ^ 2 + 1) (one_le_pow₀ hc1 (n := 2))])
      (by push_cast [← hu2]; ring)
    obtain ⟨hA3, -, hs2⟩ := greedy_step 3 4 hA2 (q' := q3)
      (by clear * - hq3 hA2; nlinarith [hA2.1]) (by push_cast [← hq3]; ring)
    obtain ⟨hA4, -, hs3⟩ := greedy_step 4 5 hA3 (q' := 6 * u4)
      (by clear * - hu4 hv3 hA3; nlinarith [hA3.1]) (by push_cast [← hu4, hv3]; ring)
    obtain ⟨hA5, -, hs4⟩ := greedy_step 5 6 hA4 (q' := 2 * k5)
      (by clear * - hk5 hA4; nlinarith [hA4.1]) (by push_cast [← hk5]; ring)
    obtain ⟨hA6, -, hs5⟩ := greedy_step 6 1 hA5 (q' := 2 * c')
      (by clear * - h7c' hA5; nlinarith [hA5.1])
      (by
        push_cast
        linear_combination 6 * (mod_cast h7c' : 7 * c' = (36 * k5 ^ 2 + 5 * k5 + 1 : ℚ)))
    rw [show 6 * (K + 1) = 6 * K + 1 + 1 + 1 + 1 + 1 + 1 by clear * -; omega,
      hs0, hs1, hs2, hs3, hs4, hs5]
    exact ih hA6 (by clear * - hc'; omega) hc'5

end GrahamCounterexample

/--
Graham has shown that $\frac{m}{n}$ is the sum of distinct unit fractions
with denominators $\equiv a\pmod{d}$ if and only if
$$\left(\frac{n}{(n,a,d)},\frac{d}{(a,d)}\right)=1.$$
Does the greedy algorithm always
terminate in such cases?

This is false: for $x = 1/119$, $a = 1$, and $d = 3$, the greedy remainder stays positive
at every multiple of $6$ steps (disproved by Ilia Pauzner using Gemini).
-/
@[category research solved, question, AMS 5]
theorem erdos_282.variants.graham :
    ¬ ∀ x : ℚ, x ∈ Set.Ioo 0 1 → ∀ a d : ℕ, 1 < d →
      (x.den / x.den.gcd (a.gcd d)).gcd (d / a.gcd d) = 1 →
      greedyUnitFractionRem { n | n ≡ a [MOD d] } x =ᶠ[atTop] 0 := by
  intro hall
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp <|
    hall (1 / 119) (by constructor <;> norm_num) 1 3 (by decide) (by norm_num)
  have hpos := pos_at_six_mul T (A := { n | n ≡ 1 [MOD 3] }) (c := 20)
    ⟨by decide, fun _ ↦ ⟨id, fun _ ↦ id⟩⟩ (by decide) (Or.inl (by decide))
  norm_num [sFrac] at hpos
  exact hpos.ne' (hT (6 * T) (by omega))

@[category test, AMS 5]
theorem greedyUnitFractionRem_sq_one : greedyUnitFractionRem { n | IsSquare n } 1 0 = 0 := by
  have : sInf {n : ℕ | IsSquare n ∧ 1 ≤ n} = 1 := IsLeast.csInf_eq <| by decide
  aesop (add simp [greedyUnitFractionRem])

/--
Graham has also shown that $x$ is the sum of distinct unit fractions with
square denominators if and only if $x\in [0,\pi^2/6-1)\cup [1,\pi^2/6)$. Does the
greedy algorithm for this always terminate? Erdős and Graham believe not - indeed, perhaps it
fails to terminate almost always.
-/
@[category research open, question, AMS 5]
theorem erdos_282.variants.sq :
    ∀ x : ℚ, (x : ℝ) ∈ Set.Ico 0 (π ^ 2 / 6 - 1) ∪ Set.Ico 1 (π ^ 2 / 6) →
      greedyUnitFractionRem { n | IsSquare n } x =ᶠ[atTop] 0 := by
  sorry

end Erdos282
