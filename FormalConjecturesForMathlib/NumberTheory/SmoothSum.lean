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

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Tactic

/-!
# Smooth sums and negative pseudosquares

Supporting definitions and proof scripts for [Erdős Problem 334](https://www.erdosproblems.com/334).
-/

@[expose] public section

/-! ===================== Part: Defs ===================== -/

section Defs

/-!
# Erdős Problem #334 — definitions and statements

Source: T. F. Bloom, *Erdős Problem #334*, https://www.erdosproblems.com/334
(accessed 2026-10-05; status on the site: **OPEN**).

> Find the best function `f(n)` such that every `n` can be written as `n = a + b`
> where both `a, b` are `f(n)`-smooth (that is, are not divisible by any prime
> `p > f(n)`).

"Find the best function" is not a yes/no statement.  We formalize the object it asks
about — the pointwise least admissible function `Erdos334.F` — and the concrete
quantitative statements mentioned on the problem page, as `Prop`s.

This file only contains *definitions* and *statements*.
Nothing in this file is claimed to be proved.
-/

open Filter Real

namespace Erdos334

/-- `a` is `y`-smooth: `a` is not divisible by any prime `p > y`.
This is the literal condition of the problem, with a real threshold `y`.
Note that `0` is never `y`-smooth (it is divisible by every prime), so this
condition automatically forces the summands to be positive. -/
def IsSmooth (y : ℝ) (a : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ a → (p : ℝ) ≤ y

/-- `n` can be written as `n = a + b` with both `a` and `b` being `y`-smooth. -/
def SumOfTwoSmooth (y : ℝ) (n : ℕ) : Prop :=
  ∃ a b : ℕ, a + b = n ∧ IsSmooth y a ∧ IsSmooth y b

/-- A function `f` is *admissible* for Erdős Problem #334 if every `n ≥ 2` can be
written as a sum of two `f(n)`-smooth numbers.  (`n = 0, 1` can never be written so,
since `0` is not smooth; hence "every `n`" has to be read as "every `n ≥ 2`".) -/
def Admissible (f : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → SumOfTwoSmooth (f n) n

/-- The *best* (pointwise smallest) admissible function: `F n` is the least natural
number `k` such that `n` is a sum of two `k`-smooth numbers.  For `n ≥ 2` the
infimum is attained (see `Erdos334.sumOfTwoSmooth_iff_F_le`); for `n < 2` the value
`sInf ∅ = 0` is a junk value that plays no role. -/
noncomputable def F (n : ℕ) : ℕ :=
  sInf {k : ℕ | SumOfTwoSmooth (k : ℝ) n}

/-! ## Statements (not proved here) -/

/-- **Balog's theorem (1989)**, as reported on the problem page (known result, *not*
proved here):
`f(n) ≪_ε n^{4/(9√e) + ε}` for every `ε > 0`.  The implied constant may depend on `ε`
but not on `n`. -/
def BalogBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    (F n : ℝ) ≤ C * (n : ℝ) ^ (4 / (9 * Real.sqrt (Real.exp 1)) + ε)

/-- **Erdős's original question** (known to be true, by Balog): `f(n) ≤ n^{1/3}`.
It is false for small `n` (e.g. `F 3 = 2 > 3^{1/3}`), so it is stated for all
sufficiently large `n`. -/
def OneThirdBound : Prop :=
  ∀ᶠ n : ℕ in atTop, (F n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 3)

/-- **Conjecture** (problem page: "It is likely that `f(n) ≤ n^{o(1)}`"), literal form:
there is a function `g = o(1)` with `F n ≤ n^{g n}` for all large `n`.  OPEN. -/
def SubpolynomialConjecture : Prop :=
  ∃ g : ℕ → ℝ, Tendsto g atTop (nhds 0) ∧ ∀ᶠ n : ℕ in atTop, (F n : ℝ) ≤ (n : ℝ) ^ g n

/-- **Conjecture attributed to Erdős** (according to a forum comment citing a paper of
Sárközy; *not* part of the problem statement, unverified attribution):
`f(n) < exp(c √(log n · log log n))` for some constant `c`.  OPEN. -/
def ErdosSarkozyConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    (F n : ℝ) < Real.exp (c * Real.sqrt (Real.log n * Real.log (Real.log n)))

end Erdos334

end Defs

/-! ===================== Part: Basic ===================== -/

section Basic

/-!
# Erdős Problem #334 — basic proved facts

These are elementary facts (proved here) that justify the formalization:
* `0` is never smooth, `1` is always smooth (so summands are automatically positive);
* `Erdos334.F` is the pointwise best admissible function
  (`Erdos334.admissible_iff`, `Erdos334.admissible_F`);
* trivial bounds `2 ≤ F n ≤ n - 1` for `n ≥ 3`.
-/

open Filter Real

namespace Erdos334

theorem not_isSmooth_zero (y : ℝ) : ¬ IsSmooth y 0 := by
  intro h
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (⌈y⌉₊ + 1)
  have := h p hp (dvd_zero p)
  have h2 : (⌈y⌉₊ : ℝ) + 1 ≤ p := by exact_mod_cast hp1
  linarith [Nat.le_ceil y]

theorem isSmooth_one (y : ℝ) : IsSmooth y 1 := by
  intro p hp hdvd
  exact absurd (Nat.le_of_dvd one_pos hdvd) (by have := hp.two_le; omega)

theorem IsSmooth.mono {y z : ℝ} {a : ℕ} (h : IsSmooth y a) (hyz : y ≤ z) : IsSmooth z a :=
  fun p hp hd => (h p hp hd).trans hyz

theorem SumOfTwoSmooth.mono {y z : ℝ} {n : ℕ} (h : SumOfTwoSmooth y n) (hyz : y ≤ z) :
    SumOfTwoSmooth z n := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  exact ⟨a, b, hab, ha.mono hyz, hb.mono hyz⟩

theorem isSmooth_self {a : ℕ} (ha : a ≠ 0) : IsSmooth (a : ℝ) a := by
  intro p _ hd
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hd

/-- For a nonnegative threshold, only its integer part matters. -/
theorem isSmooth_floor_iff {y : ℝ} (hy : 0 ≤ y) (a : ℕ) :
    IsSmooth (⌊y⌋₊ : ℝ) a ↔ IsSmooth y a := by
  constructor
  · intro h; exact h.mono (Nat.floor_le hy)
  · intro h p hp hd
    exact_mod_cast Nat.le_floor (h p hp hd)

/-- A number `a ≥ 2` which is `y`-smooth forces `y ≥ 2`. -/
theorem two_le_of_isSmooth {y : ℝ} {a : ℕ} (ha : 2 ≤ a) (h : IsSmooth y a) : 2 ≤ y := by
  have hp := Nat.minFac_prime (show a ≠ 1 by omega)
  have := h _ hp (Nat.minFac_dvd a)
  have h2 : (2 : ℝ) ≤ a.minFac := by exact_mod_cast hp.two_le
  linarith

theorem sumOfTwoSmooth_two (y : ℝ) : SumOfTwoSmooth y 2 :=
  ⟨1, 1, rfl, isSmooth_one y, isSmooth_one y⟩

/-- Trivial representation `n = 1 + (n - 1)`. -/
theorem sumOfTwoSmooth_sub_one {n : ℕ} (hn : 2 ≤ n) : SumOfTwoSmooth ((n - 1 : ℕ) : ℝ) n :=
  ⟨1, n - 1, by omega, (isSmooth_one _), isSmooth_self (by omega)⟩

/-- `n ≥ 3` written as a sum of two `y`-smooth numbers forces `y ≥ 2`. -/
theorem two_le_of_sumOfTwoSmooth {y : ℝ} {n : ℕ} (hn : 3 ≤ n) (h : SumOfTwoSmooth y n) :
    2 ≤ y := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  have ha0 : a ≠ 0 := by rintro rfl; exact not_isSmooth_zero y ha
  have hb0 : b ≠ 0 := by rintro rfl; exact not_isSmooth_zero y hb
  rcases le_or_gt 2 a with h2 | h2
  · exact two_le_of_isSmooth h2 ha
  · exact two_le_of_isSmooth (by omega) hb

theorem F_mem {n : ℕ} (hn : 2 ≤ n) : SumOfTwoSmooth ((F n : ℕ) : ℝ) n :=
  Nat.sInf_mem (s := {k : ℕ | SumOfTwoSmooth (k : ℝ) n}) ⟨_, sumOfTwoSmooth_sub_one hn⟩

/-- **Characterization of `F`.**  For `n ≥ 3` and any real threshold `y`,
`n` is a sum of two `y`-smooth numbers iff `F n ≤ y`. -/
theorem sumOfTwoSmooth_iff_F_le {n : ℕ} (hn : 3 ≤ n) (y : ℝ) :
    SumOfTwoSmooth y n ↔ (F n : ℝ) ≤ y := by
  constructor
  · intro h
    have hy : 0 ≤ y := by linarith [two_le_of_sumOfTwoSmooth hn h]
    have h' : SumOfTwoSmooth (⌊y⌋₊ : ℝ) n := by
      obtain ⟨a, b, hab, ha, hb⟩ := h
      exact ⟨a, b, hab, (isSmooth_floor_iff hy a).2 ha, (isSmooth_floor_iff hy b).2 hb⟩
    have : F n ≤ ⌊y⌋₊ := Nat.sInf_le h'
    calc (F n : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast this
      _ ≤ y := Nat.floor_le hy
  · intro h
    exact (F_mem (by omega)).mono h

theorem F_two : F 2 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le (by simpa using sumOfTwoSmooth_two 0)

/-- `F` itself is admissible. -/
theorem admissible_F : Admissible (fun n => (F n : ℝ)) := fun _ hn => F_mem hn

/-- **`F` is the best admissible function**: `f` is admissible iff `F n ≤ f n` for every
`n ≥ 3` (the value `n = 2 = 1 + 1` imposes no condition at all). -/
theorem admissible_iff (f : ℕ → ℝ) : Admissible f ↔ ∀ n : ℕ, 3 ≤ n → (F n : ℝ) ≤ f n := by
  constructor
  · intro h n hn
    exact (sumOfTwoSmooth_iff_F_le hn _).1 (h n (by omega))
  · intro h n hn
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      exact sumOfTwoSmooth_two _
    · exact (sumOfTwoSmooth_iff_F_le h3 _).2 (h n h3)

/-- Trivial upper bound. -/
theorem F_le_sub_one {n : ℕ} (hn : 2 ≤ n) : F n ≤ n - 1 :=
  Nat.sInf_le (sumOfTwoSmooth_sub_one hn)

/-- Trivial lower bound. -/
theorem two_le_F {n : ℕ} (hn : 3 ≤ n) : 2 ≤ F n := by
  have := two_le_of_sumOfTwoSmooth hn (F_mem (by omega))
  exact_mod_cast this

theorem F_three : F 3 = 2 :=
  le_antisymm (F_le_sub_one (by norm_num)) (two_le_F le_rfl)

end Erdos334

end Basic

/-! ===================== Part: Conditional ===================== -/

section Conditional

/-!
# Erdős Problem #334 — conditional results and implications between the statements

Everything in this file is **proved**, but the results are *conditional* or are
*implications between statements*; none of them resolves the open problem.

* `Erdos334.oneThirdBound_of_balogBound`: Balog's bound implies Erdős's `n^{1/3}` bound.
* `Erdos334.subpolynomialConjecture_iff`: the `n^{o(1)}` conjecture in `ε`-form.
* `Erdos334.subpolynomialConjecture_of_erdosSarkozy`,
  `Erdos334.oneThirdBound_of_subpolynomialConjecture`.
* `Erdos334.exists_prime_nonresidue_le_of_sumOfTwoSmooth` and
  `Erdos334.eventually_small_nonresidue_of_eventually_sumOfTwoSmooth`: the argument
  from a forum comment (Woett, 19 Nov 2025) that strong bounds for this problem imply
  small quadratic non-residues modulo primes `p ≡ 3 (mod 4)`.
-/

open Filter Real

namespace Erdos334

/-! ## Balog ⟹ `n^{1/3}` -/

theorem balog_exponent_lt_one_third : 4 / (9 * Real.sqrt (Real.exp 1)) < 1 / 3 := by
  have he : (4 / 3 : ℝ) ^ 2 < Real.exp 1 := by
    have := Real.exp_one_gt_d9; norm_num at *; linarith
  have hs : 4 / 3 < Real.sqrt (Real.exp 1) := Real.lt_sqrt (by norm_num) |>.2 he
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- Balog's theorem implies (an affirmative answer to) Erdős's original question. -/
theorem oneThirdBound_of_balogBound (h : BalogBound) : OneThirdBound := by
  set θ := 4 / (9 * Real.sqrt (Real.exp 1)) with hθ
  set ε := (1 / 3 - θ) / 2 with hε
  have hεpos : 0 < ε := by have := balog_exponent_lt_one_third; rw [hε]; linarith
  obtain ⟨C, hC⟩ := h ε hεpos
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hεpos).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop C, eventually_ge_atTop 2] with n hn h2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsplit : (n : ℝ) ^ ((1 : ℝ) / 3) = (n : ℝ) ^ ε * (n : ℝ) ^ (θ + ε) := by
    rw [← Real.rpow_add hn0]; congr 1; rw [hε]; ring
  rw [hsplit]
  calc (F n : ℝ) ≤ C * (n : ℝ) ^ (θ + ε) := hC n h2
    _ ≤ (n : ℝ) ^ ε * (n : ℝ) ^ (θ + ε) :=
        mul_le_mul_of_nonneg_right hn (by positivity)

/-! ## The `n^{o(1)}` conjecture -/

/-- The literal `n^{o(1)}` form is equivalent to the `ε`-form
`∀ ε > 0, F n ≤ n^ε` for all large `n`. -/
theorem subpolynomialConjecture_iff :
    SubpolynomialConjecture ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (F n : ℝ) ≤ (n : ℝ) ^ ε := by
  constructor
  · rintro ⟨g, hg, hF⟩ ε hε
    filter_upwards [hF, (tendsto_order.1 hg).2 ε hε, eventually_ge_atTop 1] with n h1 h2 h3
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast h3
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hn h2.le)
  · intro h
    refine ⟨fun n => Real.log (F n) / Real.log n, ?_, ?_⟩
    · rw [tendsto_order]
      constructor
      · intro a ha
        filter_upwards [eventually_ge_atTop 3] with n hn
        have hF : (1 : ℝ) ≤ F n := by exact_mod_cast (show 1 ≤ F n by have := two_le_F hn; omega)
        have : 0 ≤ Real.log (F n) / Real.log n :=
          div_nonneg (Real.log_nonneg hF) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
        linarith
      · intro b hb
        filter_upwards [h (b / 2) (by positivity), eventually_ge_atTop 3] with n h1 hn
        have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
        have hlog : 0 < Real.log n := Real.log_pos hn1
        have hF : (0 : ℝ) < F n := by exact_mod_cast (show 0 < F n by have := two_le_F hn; omega)
        have : Real.log (F n) ≤ b / 2 * Real.log n := by
          have := Real.log_le_log hF h1
          rwa [Real.log_rpow (by linarith)] at this
        rw [div_lt_iff₀ hlog]
        nlinarith
    · filter_upwards [eventually_ge_atTop 3] with n hn
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have hlog : 0 < Real.log n := Real.log_pos hn1
      have hF : (0 : ℝ) < F n := by exact_mod_cast (show 0 < F n by have := two_le_F hn; omega)
      rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hlog.ne', Real.exp_log hF]

/-- The `n^{o(1)}` conjecture implies Erdős's `n^{1/3}` bound. -/
theorem oneThirdBound_of_subpolynomialConjecture (h : SubpolynomialConjecture) :
    OneThirdBound :=
  subpolynomialConjecture_iff.1 h (1 / 3) (by norm_num)

/-- The `exp(c √(log n log log n))` conjecture implies the `n^{o(1)}` conjecture. -/
theorem subpolynomialConjecture_of_erdosSarkozy (h : ErdosSarkozyConjecture) :
    SubpolynomialConjecture := by
  rw [subpolynomialConjecture_iff]
  obtain ⟨c, hc, hF⟩ := h
  intro ε hε
  set δ := (ε / c) ^ 2 with hδ
  have hδpos : 0 < δ := by positivity
  -- `log L ≤ δ L` for all large `L`
  have hlogL : ∀ᶠ L : ℝ in atTop, Real.log L ≤ δ * L := by
    have := Real.isLittleO_log_id_atTop.bound hδpos
    filter_upwards [this, eventually_ge_atTop 1] with L h1 h2
    have h3 : 0 ≤ Real.log L := Real.log_nonneg h2
    simpa [abs_of_nonneg h3, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L)] using h1
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hF, hlogn.eventually hlogL, hlogn.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with n h1 h2 h3 h4
  set L := Real.log n
  have hn : (0 : ℝ) < n := by exact_mod_cast h4
  refine h1.le.trans ?_
  rw [Real.rpow_def_of_pos hn, Real.exp_le_exp]
  have hLL : 0 ≤ Real.log L := Real.log_nonneg h3
  have key : Real.sqrt (L * Real.log L) ≤ ε / c * L := by
    rw [Real.sqrt_le_left (by positivity)]
    calc L * Real.log L ≤ L * (δ * L) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = (ε / c * L) ^ 2 := by rw [hδ]; ring
  calc c * Real.sqrt (L * Real.log L) ≤ c * (ε / c * L) := mul_le_mul_of_nonneg_left key hc.le
    _ = L * ε := by field_simp

/-! ## Woett's remark: small quadratic non-residues -/

theorem isSquare_of_isSmooth {p : ℕ} {y : ℝ}
    (hsq : ∀ q : ℕ, q.Prime → (q : ℝ) ≤ y → IsSquare (q : ZMod p)) :
    ∀ a : ℕ, IsSmooth y a → IsSquare (a : ZMod p) := by
  intro a
  induction a using induction_on_primes with
  | zero => intro _; exact ⟨0, by simp⟩
  | one => intro _; exact ⟨1, by simp⟩
  | prime_mul q a hq ih =>
    intro h
    have hqa : IsSquare (q : ZMod p) := hsq q hq (h q hq (dvd_mul_right q a))
    have ha : IsSquare (a : ZMod p) := ih (fun r hr hd => h r hr (dvd_mul_of_dvd_right hd q))
    push_cast
    exact hqa.mul ha

/-- **Woett's remark, pointwise form.**  If a prime `p ≡ 3 (mod 4)` is a sum of two
`y`-smooth numbers, then there is a prime `q ≤ y` which is a quadratic non-residue
modulo `p`. -/
theorem exists_prime_nonresidue_le_of_sumOfTwoSmooth {p : ℕ} [hp : Fact p.Prime]
    (h4 : p % 4 = 3) {y : ℝ} (h : SumOfTwoSmooth y p) :
    ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ y ∧ ¬ IsSquare (q : ZMod p) := by
  by_contra hne
  push Not at hne
  obtain ⟨a, b, hab, ha, hb⟩ := h
  have hb0 : b ≠ 0 := by rintro rfl; exact not_isSmooth_zero y hb
  have ha0 : a ≠ 0 := by rintro rfl; exact not_isSmooth_zero y ha
  obtain ⟨x, hx⟩ := isSquare_of_isSmooth (fun q hq hqy => hne q hq hqy) a ha
  obtain ⟨z, hz⟩ := isSquare_of_isSmooth (fun q hq hqy => hne q hq hqy) b hb
  have hbz : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hd
    omega
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz; exact hbz hz
  have hsum : (a : ZMod p) + b = 0 := by
    rw [← Nat.cast_add, hab, ZMod.natCast_self]
  have : IsSquare (-1 : ZMod p) := by
    refine ⟨x / z, ?_⟩
    rw [hx, hz] at hsum
    field_simp
    linear_combination -hsum
  exact (ZMod.exists_sq_eq_neg_one_iff.1 this) h4

/-- `F`-form of Woett's remark: for a prime `p ≡ 3 (mod 4)` there is a quadratic
non-residue modulo `p` which is a prime `≤ F p`. -/
theorem exists_prime_nonresidue_le_F {p : ℕ} [hp : Fact p.Prime] (h4 : p % 4 = 3) :
    ∃ q : ℕ, q.Prime ∧ q ≤ F p ∧ ¬ IsSquare (q : ZMod p) := by
  obtain ⟨q, hq, hqF, hns⟩ :=
    exists_prime_nonresidue_le_of_sumOfTwoSmooth h4 (F_mem hp.out.two_le)
  exact ⟨q, hq, by exact_mod_cast hqF, hns⟩

/-- **Woett's remark** (forum comment, 19 Nov 2025), with an arbitrary exponent `θ`
(the comment uses `θ = 0.1`): if every sufficiently large `n` is a sum of two
`n^θ`-smooth numbers, then every sufficiently large prime `p ≡ 3 (mod 4)` has a
quadratic non-residue (indeed a prime one) `q ≤ p^θ`. -/
theorem eventually_small_nonresidue_of_eventually_sumOfTwoSmooth (θ : ℝ)
    (h : ∀ᶠ n : ℕ in atTop, SumOfTwoSmooth ((n : ℝ) ^ θ) n) :
    ∀ᶠ p : ℕ in atTop, p.Prime → p % 4 = 3 →
      ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ (p : ℝ) ^ θ ∧ ¬ IsSquare (q : ZMod p) := by
  filter_upwards [h] with p hp hprime h4
  have := Fact.mk hprime
  exact exists_prime_nonresidue_le_of_sumOfTwoSmooth h4 hp

end Erdos334

end Conditional

/-! ===================== Part: Pseudosquare ===================== -/

section Pseudosquare

/-!
# Erdős Problem #334 — the OEIS claim `A062241(n) ≤ A045535(n-1)` from the forum

A forum comment (my99n, 3 Mar 2026) claims that OEIS `A062241` is bounded by OEIS
`A045535`; the OEIS entry `A062241` records this as `a(n) ≤ A045535(n-1)`
(Touch Sungkawichai, Mar 05 2026).  We formalize both sequences from their OEIS
definitions and **prove** the claimed inequality.

* `A062241 n`: smallest integer `≥ 2` that is not the sum of two positive integers whose
  prime factors are all `≤ prime(n)`, where (OEIS convention) `prime(0) = 1`.
* `A045535 n`: smallest positive `m` with `m ≡ 7 (mod 8)` such that for each of the first
  `n` odd primes `p`, `-m` is a nonzero quadratic residue modulo `p`.

Key fact (`Erdos334.not_sumOfTwoSmooth_of_negPseudosquare`): if `m ≡ 7 (mod 8)` and `-m`
is a nonzero square modulo every odd prime `p ≤ P`, then `m` is not a sum of two
`P`-smooth numbers.  The proof uses the Jacobi symbol and quadratic reciprocity.
-/

open ZMod

namespace Erdos334

/-- OEIS convention for `A062241`: `prime(0) = 1`, `prime(n) =` the `n`-th prime
(`prime(1) = 2`). -/
noncomputable def oeisPrime (n : ℕ) : ℕ :=
  if n = 0 then 1 else Nat.nth Nat.Prime (n - 1)

/-- OEIS `A062241`. -/
noncomputable def A062241 (n : ℕ) : ℕ :=
  sInf {m : ℕ | 2 ≤ m ∧ ¬ SumOfTwoSmooth (oeisPrime n : ℝ) m}

/-- `m ≡ 7 (mod 8)` and `-m` is a nonzero quadratic residue modulo each of the first `n`
odd primes `Nat.nth Nat.Prime 1 = 3, Nat.nth Nat.Prime 2 = 5, …`. -/
def IsNegPseudosquare (n m : ℕ) : Prop :=
  m % 8 = 7 ∧ ∀ i < n,
    IsSquare (-(m : ZMod (Nat.nth Nat.Prime (i + 1)))) ∧ (m : ZMod (Nat.nth Nat.Prime (i + 1))) ≠ 0

/-- OEIS `A045535`: least negative pseudosquare modulo the first `n` odd primes. -/
noncomputable def A045535 (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ IsNegPseudosquare n m}

/-! ## Jacobi symbol computations -/

theorem jacobiSym_eq_one_of_isSmooth {x : ℤ} {P : ℝ}
    (hq : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ P → jacobiSym x p = 1) :
    ∀ a : ℕ, a % 2 = 1 → IsSmooth P a → jacobiSym x a = 1 := by
  intro a
  induction a using induction_on_primes with
  | zero => intro h; simp at h
  | one => intro _ _; exact jacobiSym.one_right x
  | prime_mul q a hq' ih =>
    intro hodd h
    have hq2 : q ≠ 2 := by rintro rfl; omega
    have haodd : a % 2 = 1 := Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_iff.2 hodd)).2
    rw [jacobiSym.mul_right' x hq'.ne_zero (by omega), hq q hq' hq2 (h q hq' (dvd_mul_right q a)),
      ih haodd (fun r hr hd => h r hr (dvd_mul_of_dvd_right hd q)), one_mul]

/-- Core parity/reciprocity computation. -/
theorem negPseudosquare_core (a c k m : ℕ) (ha : a % 2 = 1) (hc : c % 2 = 1) (hk : 1 ≤ k)
    (hm : a + 2 ^ k * c = m) (h8 : m % 8 = 7)
    (h1 : jacobiSym (-(m : ℤ)) a = 1) (h2 : jacobiSym (-(m : ℤ)) c = 1) : False := by
  have e1 : jacobiSym (-(m : ℤ)) a = χ₄ a * χ₈ a ^ k * jacobiSym c a := by
    have : -(m : ℤ) = (-1) * 2 ^ k * c + a * (-1) := by rw [← hm]; push_cast; ring
    rw [jacobiSym.mod_left, this, Int.add_mul_emod_self_left, ← jacobiSym.mod_left,
      jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.pow_left,
      jacobiSym.at_neg_one (Nat.odd_iff.2 ha), jacobiSym.at_two (Nat.odd_iff.2 ha)]
  have e2 : jacobiSym (-(m : ℤ)) c = χ₄ c * jacobiSym a c := by
    have : -(m : ℤ) = (-1) * a + c * (-(2 ^ k)) := by rw [← hm]; push_cast; ring
    rw [jacobiSym.mod_left, this, Int.add_mul_emod_self_left, ← jacobiSym.mod_left,
      jacobiSym.mul_left, jacobiSym.at_neg_one (Nat.odd_iff.2 hc)]
  have qr := jacobiSym.quadratic_reciprocity_if ha hc
  rw [e1] at h1
  rw [e2] at h2
  rw [χ₄_nat_eq_if_mod_four, χ₈_nat_eq_if_mod_eight] at h1
  rw [χ₄_nat_eq_if_mod_four] at h2
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases j with _ | _ | j
  · -- k = 1
    simp only [zero_add, pow_one] at hm h1
    split_ifs at h1 h2 qr <;> omega
  · -- k = 2
    simp only [zero_add, Nat.reduceAdd] at hm h1
    split_ifs at h1 h2 qr <;> omega
  · -- k ≥ 3
    have hm' : a + 8 * (2 ^ j * c) = m := by rw [← hm]; ring
    split_ifs at h1 h2 qr <;> first | omega | (norm_num at h1; omega)

/-- **Key lemma.**  If `m ≡ 7 (mod 8)` and `-m` is a nonzero square modulo every odd prime
`p ≤ P`, then `m` is not a sum of two `P`-smooth numbers. -/
theorem not_sumOfTwoSmooth_of_negPseudosquare {P : ℝ} {m : ℕ} (h8 : m % 8 = 7)
    (hq : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ P →
      IsSquare (-(m : ZMod p)) ∧ (m : ZMod p) ≠ 0) :
    ¬ SumOfTwoSmooth P m := by
  have hJ : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ P → jacobiSym (-(m : ℤ)) p = 1 := by
    intro p hp hp2 hpP
    have := Fact.mk hp
    obtain ⟨hsq, hne⟩ := hq p hp hp2 hpP
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    have hcast : (((-(m : ℤ)) : ℤ) : ZMod p) = -(m : ZMod p) := by push_cast; rfl
    rw [legendreSym.eq_one_iff p (by rw [hcast]; exact neg_ne_zero.2 hne), hcast]
    exact hsq
  have key : ∀ a b : ℕ, a % 2 = 1 → a + b = m → IsSmooth P a → IsSmooth P b → False := by
    intro a b ha hab sa sb
    have hb0 : b ≠ 0 := by rintro rfl; exact not_isSmooth_zero P sb
    obtain ⟨k, c, hc, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hb0
    have hc2 : c % 2 = 1 := Nat.odd_iff.1 hc
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hab; omega
      · exact hk
    have sc : IsSmooth P c := fun p hp hd => sb p hp (dvd_mul_of_dvd_right hd _)
    exact negPseudosquare_core a c k m ha hc2 hk hab h8
      (jacobiSym_eq_one_of_isSmooth hJ a ha sa) (jacobiSym_eq_one_of_isSmooth hJ c hc2 sc)
  rintro ⟨a, b, hab, sa, sb⟩
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · exact key b a (by omega) (by omega) sb sa
  · exact key a b ha hab sa sb

/-- `A045535 n` is well defined: `8 · 3 · 5 ⋯ p_n - 1` is a negative pseudosquare. -/
theorem exists_negPseudosquare (n : ℕ) : ∃ m : ℕ, 0 < m ∧ IsNegPseudosquare n m := by
  set N := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime (i + 1) with hN
  have hNpos : 0 < N := Finset.prod_pos fun i _ => (Nat.prime_nth_prime (i + 1)).pos
  refine ⟨8 * N - 1, by omega, by omega, fun i hi => ?_⟩
  set q := Nat.nth Nat.Prime (i + 1)
  have : Fact q.Prime := ⟨Nat.prime_nth_prime (i + 1)⟩
  have hdvd : q ∣ 8 * N := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (by simpa using hi)) 8
  have hm1 : ((8 * N - 1 : ℕ) : ZMod q) = -1 := by
    have : ((8 * N - 1 + 1 : ℕ) : ZMod q) = 0 := by
      rw [Nat.sub_add_cancel (by omega), ZMod.natCast_eq_zero_iff]; exact hdvd
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  rw [hm1, neg_neg]
  exact ⟨⟨1, by simp⟩, by simp⟩

/-- **The forum/OEIS claim**: `A062241(n) ≤ A045535(n-1)` for every `n ≥ 1`. -/
theorem A062241_le_A045535 (n : ℕ) (hn : 1 ≤ n) : A062241 n ≤ A045535 (n - 1) := by
  have hmem : 0 < A045535 (n - 1) ∧ IsNegPseudosquare (n - 1) (A045535 (n - 1)) :=
    Nat.sInf_mem (exists_negPseudosquare (n - 1))
  obtain ⟨_, h8, hq⟩ := hmem
  apply Nat.sInf_le
  refine ⟨by omega, not_sumOfTwoSmooth_of_negPseudosquare h8 ?_⟩
  intro p hp hp2 hpP
  have hP : oeisPrime n = Nat.nth Nat.Prime (n - 1) := by
    simp [oeisPrime, show n ≠ 0 by omega]
  rw [hP] at hpP
  have hpP' : p ≤ Nat.nth Nat.Prime (n - 1) := by exact_mod_cast hpP
  set k := Nat.count Nat.Prime p
  have hk : Nat.nth Nat.Prime k = p := Nat.nth_count hp
  have hkn : k ≤ n - 1 := by
    rw [← Nat.nth_le_nth Nat.infinite_setOfPred_prime, hk]; exact hpP'
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0, Nat.nth_prime_zero_eq_two] at hk; exact hp2 hk.symm
  have := hq (k - 1) (by omega)
  rwa [show k - 1 + 1 = k by omega, hk] at this

/-! ## Sanity checks of the OEIS definitions against the OEIS data -/

theorem A045535_zero : A045535 0 = 7 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by norm_num, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  · exact le_csInf ⟨7, by norm_num, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      (fun m ⟨_, h8, _⟩ => by omega)

theorem isSmooth_two_two_pow (j : ℕ) : IsSmooth 2 (2 ^ j) := by
  intro p hp hd
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
  subst this; norm_num

theorem A062241_one : A062241 1 = 7 := by
  have hP : (oeisPrime 1 : ℝ) = 2 := by simp [oeisPrime, Nat.nth_prime_zero_eq_two]
  apply le_antisymm
  · simpa [A045535_zero] using A062241_le_A045535 1 le_rfl
  · refine le_csInf ⟨7, by norm_num, ?_⟩ ?_
    · rw [hP]
      exact not_sumOfTwoSmooth_of_negPseudosquare (by norm_num)
        (fun p hp hp2 hpP => absurd (by exact_mod_cast hpP : p ≤ 2) (by have := hp.two_le; omega))
    · rintro m ⟨hm2, hm⟩
      rw [hP] at hm
      by_contra hlt
      have s := isSmooth_two_two_pow
      interval_cases m
      · exact hm ⟨1, 1, rfl, by simpa using s 0, by simpa using s 0⟩
      · exact hm ⟨1, 2, rfl, by simpa using s 0, by simpa using s 1⟩
      · exact hm ⟨2, 2, rfl, by simpa using s 1, by simpa using s 1⟩
      · exact hm ⟨1, 4, rfl, by simpa using s 0, by simpa using s 2⟩
      · exact hm ⟨2, 4, rfl, by simpa using s 1, by simpa using s 2⟩

end Erdos334

end Pseudosquare
