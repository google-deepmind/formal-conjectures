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
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The `p`-adic logarithm and exponential

The `p`-adic logarithm `log u = ∑ (-1)ⁿ (u - 1)^(n+1) / (n+1)` and exponential `exp w = ∑ wⁿ / n!`
over an abstract complete ultrametric field `K` of characteristic zero with `‖p‖ < 1`, e.g. a
finite extension of `ℚ_p` or the field `ℂ_[p]` of `p`-adic complex numbers.

## Main definitions

* `padicLog`: the logarithm series, converging on the whole open disc `‖u - 1‖ < 1`.
* `padicExp`: the exponential series, converging on `‖w‖ ^ 2 < ‖p‖` (for odd `p`).
* `HasIwasawaLog p x`: some power `x ^ N` (`N ≥ 1`) is a `1`-unit times a power of `p`.
* `iwasawaLog p`: the Iwasawa logarithm, the extension of `padicLog` to `HasIwasawaLog p` which is
  a homomorphism and satisfies `log p = 0`.

## Main results

* `tendsto_padicLog`: `log u = limₖ (u^(pᵏ) - 1)/pᵏ` on the whole disc, for every prime `p`.
* `padicLog_mul`: `log (u * v) = log u + log v` on the whole disc, for every prime `p`.
* `iwasawaLog_mul`, `iwasawaLog_natCast_p`: the Iwasawa logarithm is a homomorphism with
  `log p = 0`.
* `PadicComplex.hasIwasawaLog_iff`: every nonzero element of `ℂ_[p]` has an Iwasawa logarithm.
* `padicExp_add`, `padicLog_padicExp`, `padicExp_padicLog`: for odd `p`, `exp` and `log` are
  mutually inverse homomorphisms between the discs `‖w‖ ^ 2 < ‖p‖` and `‖u - 1‖ ^ 2 < ‖p‖`.

The odd-`p` restriction on the exponential side enters only through the Legendre-type bound
`2 v_p(n!) ≤ n - 1`, which fails at `p = 2`.

## References

* [Con] K. Conrad, *Infinite series in p-adic fields*, §8 (the logarithm) and §4 (the exponential).
* [Kob84] N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Ch. IV.
* [Wiki] Wikipedia, *p-adic exponential function* (the Iwasawa logarithm).
-/

@[expose] public section

open Filter Topology

open scoped Nat

namespace PadicExpLog

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

section ResidueChar

variable (h3 : ‖((p : ℕ) : K)‖ < 1)
include h3

omit hp [CompleteSpace K] [CharZero K] in
set_option linter.unusedSectionVars false in
/-- If `‖p‖ < 1` in an ultrametric field, every natural number coprime to `p` has norm
one.  (Ultrametricity gives `‖n‖ ≤ 1`; if also `‖n‖ < 1` with `gcd n p = 1`, Bézout makes
`‖1‖ < 1`.) -/
theorem norm_natCast_eq_one_of_coprime {n : ℕ} (hn : n.Coprime p) : ‖(n : K)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K n) (not_lt.mp fun hlt => ?_)
  have hb := Nat.gcd_eq_gcd_ab n p
  rw [hn, Nat.cast_one] at hb
  have h1 : (1 : K) = (n : K) * ((n.gcdA p : ℤ) : K) + ((p : ℕ) : K) * ((n.gcdB p : ℤ) : K) := by
    have := congrArg (fun z : ℤ => (z : K)) hb
    push_cast at this
    simpa using this
  have h2 : (1 : ℝ) ≤
      max (‖(n : K)‖ * ‖((n.gcdA p : ℤ) : K)‖) (‖((p : ℕ) : K)‖ * ‖((n.gcdB p : ℤ) : K)‖) := by
    calc (1 : ℝ) = ‖(1 : K)‖ := norm_one.symm
      _ = ‖(n : K) * ((n.gcdA p : ℤ) : K) + ((p : ℕ) : K) * ((n.gcdB p : ℤ) : K)‖ := by rw [← h1]
      _ ≤ _ := by
          simpa only [norm_mul] using IsUltrametricDist.norm_add_le_max
            ((n : K) * ((n.gcdA p : ℤ) : K)) (((p : ℕ) : K) * ((n.gcdB p : ℤ) : K))
  refine absurd h2 (not_le.mpr (max_lt ?_ ?_))
  · calc ‖(n : K)‖ * ‖((n.gcdA p : ℤ) : K)‖ ≤ ‖(n : K)‖ * 1 :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one K _) (norm_nonneg _)
    _ < 1 := by simpa using hlt
  · calc ‖((p : ℕ) : K)‖ * ‖((n.gcdB p : ℤ) : K)‖ ≤ ‖((p : ℕ) : K)‖ * 1 :=
        mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one K _) (norm_nonneg _)
    _ < 1 := by simpa using h3

omit [CompleteSpace K] [CharZero K] in
/-- `‖n‖ = ‖p‖ ^ v_p(n)` for `0 < n`: the norm on `ℕ ⊆ K` is determined by `‖p‖`. -/
theorem norm_natCast_eq_pow_padicValNat {n : ℕ} (hn : n ≠ 0) :
    ‖(n : K)‖ = ‖((p : ℕ) : K)‖ ^ padicValNat p n := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  push_cast
  rw [norm_mul, norm_pow,
    norm_natCast_eq_one_of_coprime h3 ((Nat.coprime_ordCompl hp.out hn).symm),
    mul_one, Nat.factorization_def n hp.out]

omit [CompleteSpace K] [CharZero K] in
/-- Legendre bound in norm form: `‖(n! : K)‖ ≥ ‖p‖ ^ ((n - 1) / 2)` — more precisely
`‖p‖ ^ (n - 1) ≤ ‖(n !) : K‖ ^ 2`, the squared form avoiding half-integer exponents.
From `v_p(n!) = (n - s_p(n)) / 2 ≤ (n - 1) / 2` for `n ≥ 1`. -/
theorem sq_norm_factorial_ge (hp2 : p ≠ 2) {n : ℕ} (hn : n ≠ 0) :
    ‖((p : ℕ) : K)‖ ^ (n - 1) ≤ ‖((n ! : ℕ) : K)‖ ^ 2 := by
  have hleg := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) hn
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have h2v : 2 * padicValNat p (n !) ≤ (p - 1) * padicValNat p (n !) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [norm_natCast_eq_pow_padicValNat h3 n.factorial_ne_zero, ← pow_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) h3.le (by omega)

end ResidueChar

section NatAux

omit hp in
/-- `2 v ≤ p ^ v` for `p ≥ 2`. -/
private lemma two_mul_le_pow (hp2 : 2 ≤ p) (v : ℕ) : 2 * v ≤ p ^ v := by
  have h2 : 2 * v ≤ 2 ^ v := by
    induction v with
    | zero => simp
    | succ k ih =>
        have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
        rw [pow_succ]
        omega
  exact h2.trans (Nat.pow_le_pow_left hp2 v)

omit hp in
/-- `4 v ≤ p ^ v + 3` for `p ≥ 3`. -/
private lemma four_mul_le_pow_add (hp3 : 3 ≤ p) (v : ℕ) : 4 * v ≤ p ^ v + 3 := by
  have h3 : 4 * v ≤ 3 ^ v + 3 := by
    induction v with
    | zero => simp
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num
      · have h1 : 3 ≤ 3 ^ k := by
          calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
            _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        rw [pow_succ]
        omega
  exact h3.trans (by
    have := Nat.pow_le_pow_left hp3 v
    omega)

omit hp in
/-- `p ^ v_p(m) ≤ m` for `m ≠ 0`. -/
private lemma pow_padicValNat_le {m : ℕ} (hm : m ≠ 0) : p ^ padicValNat p m ≤ m :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hm) pow_padicValNat_dvd

/-- `2 v_p(m) ≤ m` for `m ≠ 0`. -/
private lemma two_mul_padicValNat_le {m : ℕ} (hm : m ≠ 0) :
    2 * padicValNat p m ≤ m := by
  have h1 := two_mul_le_pow (p := p) hp.out.two_le (padicValNat p m)
  have h2 := pow_padicValNat_le (p := p) hm
  omega

/-- `4 v_p(m) ≤ m + 3` for `m ≠ 0` at `p ≥ 3`: quantitative form of `m - 2 v_p(m) → ∞`. -/
private lemma four_mul_padicValNat_le (hp2 : p ≠ 2) {m : ℕ} (hm : m ≠ 0) :
    4 * padicValNat p m ≤ m + 3 := by
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have h1 := four_mul_le_pow_add (p := p) hp3 (padicValNat p m)
  have h2 := pow_padicValNat_le (p := p) hm
  omega

omit hp in
/-- `v_p(n + 1) ≤ n`. -/
private lemma padicValNat_succ_le (n : ℕ) : padicValNat p (n + 1) ≤ n :=
  Nat.lt_succ_iff.mp <| (padicValNat_le_nat_log (n + 1)).trans_lt
    (Nat.log_lt_self p n.succ_ne_zero)

end NatAux

section LogExp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `((p : ℕ) : K) ≠ 0` in characteristic zero, so `‖p‖ > 0`. -/
private lemma norm_natCast_p_pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ :=
  norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.pos.ne')

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The ultrametric logarithm `log u = -∑ₙ (1 - u)^(n+1) / (n+1)`, converging for
`‖u - 1‖ < 1`; junk value otherwise.  [Kob84, Ch. IV §1]. -/
noncomputable def padicLog (u : K) : K :=
  -∑' n : ℕ, (1 - u) ^ (n + 1) / (n + 1)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The ultrametric exponential `exp w = ∑ₙ wⁿ / n!`, converging for
`‖w‖ < ‖p‖^(1/2)`; junk value otherwise.  [Kob84, Ch. IV §1]. -/
noncomputable def padicExp (w : K) : K :=
  ∑' n : ℕ, w ^ n / (n ! : ℕ)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
set_option linter.unusedSectionVars false in
/-- `log 1 = 0`: every term of the series vanishes. -/
@[simp] theorem padicLog_one : padicLog (1 : K) = 0 := by
  simp [padicLog]

omit [IsUltrametricDist K] [CompleteSpace K] in
set_option linter.unusedSectionVars false in
/-- `exp 0 = 1`: only the constant term survives. -/
@[simp] theorem padicExp_zero : padicExp (0 : K) = 1 := by
  rw [padicExp, tsum_eq_single 0 fun b hb => by simp [zero_pow hb]]
  simp

omit [CompleteSpace K] [CharZero K] in
/-- A `1`-unit has norm one: `‖1 + x‖ = 1` as soon as `‖x‖ < 1`. -/
theorem norm_eq_one_of_norm_sub_one_lt_one {u : K} (hu : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have h : u = 1 + (u - 1) := by ring
  rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hu.ne'),
    norm_one, max_eq_left hu.le]

omit [CompleteSpace K] [CharZero K] in
/-- Dominated convergence for series in an ultrametric group: if all the families `F k` and the
limit family `G` are dominated by one `B` with `B → 0`, and `F k j → G j` for each fixed `j`,
then `∑' j, F k j → ∑' j, G j`.  (Elementary here: an ultrametric series is bounded by the sup
of its terms, so the domination controls the whole tail at once.) -/
private lemma tendsto_tsum_of_forall_norm_le {F : ℕ → ℕ → K} {G : ℕ → K} {B : ℕ → ℝ}
    (hF : ∀ k, Summable (F k)) (hG : Summable G) (hFB : ∀ k j, ‖F k j‖ ≤ B j)
    (hGB : ∀ j, ‖G j‖ ≤ B j) (hB : Tendsto B atTop (𝓝 0))
    (hlim : ∀ j, Tendsto (fun k => F k j) atTop (𝓝 (G j))) :
    Tendsto (fun k => ∑' j, F k j) atTop (𝓝 (∑' j, G j)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hB (ε / 2) (by linarith)
  have hfin : ∀ᶠ k in atTop, ∀ j ∈ Finset.range J, ‖F k j - G j‖ ≤ ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro j _
    have h0 : Tendsto (fun k => ‖F k j - G j‖) atTop (𝓝 0) := by
      simpa using ((hlim j).sub (tendsto_const_nhds (x := G j))).norm
    exact (h0.eventually_lt_const (show (0 : ℝ) < ε / 2 by linarith)).mono fun k hk => hk.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hfin
  refine ⟨N, fun k hk => ?_⟩
  have hterm : ∀ j, ‖F k j - G j‖ ≤ ε / 2 := by
    intro j
    rcases lt_or_ge j J with hj | hj
    · exact hN k hk j (Finset.mem_range.2 hj)
    · have hBj : B j ≤ ε / 2 := by
        have h := hJ j hj
        rw [Real.dist_eq, sub_zero] at h
        exact (le_abs_self _).trans h.le
      calc ‖F k j - G j‖ = ‖F k j + -G j‖ := by rw [sub_eq_add_neg]
        _ ≤ max ‖F k j‖ ‖-G j‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ ε / 2 := max_le ((hFB k j).trans hBj) (by rw [norm_neg]; exact (hGB j).trans hBj)
  calc dist (∑' j, F k j) (∑' j, G j) = ‖∑' j, (F k j - G j)‖ := by
        rw [(hF k).tsum_sub hG, dist_eq_norm]
    _ ≤ ε / 2 := IsUltrametricDist.norm_tsum_le_of_forall_le hterm
    _ < ε := by linarith

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `∏_{i < j} (-1 - i) = (-1)^j j !`: the value at `-1` of the polynomial `∏_{i<j} (X - i)`. -/
private lemma prod_range_neg_one_sub (j : ℕ) :
    (∏ i ∈ Finset.range j, ((-1 : K) - (i : K))) = (-1 : K) ^ j * ((j ! : ℕ) : K) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The binomial coefficient as a polynomial in its upper index:
`C(M, j) · j ! = ∏_{i < j} (M - i)` in a characteristic-zero field, for `j ≤ M`. -/
private lemma cast_choose_mul_factorial {M j : ℕ} (hj : j ≤ M) :
    ((M.choose j : ℕ) : K) * ((j ! : ℕ) : K) = ∏ i ∈ Finset.range j, ((M : K) - (i : K)) := by
  have h1 : ((M.descFactorial j : ℕ) : K) = ((j ! : ℕ) : K) * ((M.choose j : ℕ) : K) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have h2 : ((M.descFactorial j : ℕ) : K) = ∏ i ∈ Finset.range j, ((M : K) - (i : K)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    exact Finset.prod_congr rfl fun i hi =>
      Nat.cast_sub (le_trans (Finset.mem_range.mp hi).le hj)
  rw [← h2, h1, mul_comm]

end LogExp

/-! ### The unit disc is a group -/

section OneUnits

omit [CompleteSpace K] [CharZero K] in
/-- `‖xy - 1‖ = ‖(x - 1)y + (y - 1)‖ ≤ max (‖x - 1‖ ‖y‖) ‖y - 1‖ < 1`. [Con, p. 27]. -/
theorem norm_mul_sub_one_lt {u v : K} (hu : ‖u - 1‖ < 1) (hv : ‖v - 1‖ < 1) :
    ‖u * v - 1‖ < 1 := by
  have h : u * v - 1 = (u - 1) * v + (v - 1) := by ring
  rw [h]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hv)
  rw [norm_mul, norm_eq_one_of_norm_sub_one_lt_one hv, mul_one]
  exact hu

omit [CompleteSpace K] [CharZero K] in
/-- Sharp form of `norm_mul_sub_one_lt`: if `‖v‖ ≤ 1` then `u * v` is at least as close to `1`
as the further of `u` and `v` is, since `u * v - 1 = (u - 1) * v + (v - 1)`. -/
theorem norm_mul_sub_one_le_max {u v : K} (hv : ‖v‖ ≤ 1) :
    ‖u * v - 1‖ ≤ max ‖u - 1‖ ‖v - 1‖ := by
  have h : u * v - 1 = (u - 1) * v + (v - 1) := by ring
  rw [h]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ le_rfl)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hv

omit [CompleteSpace K] [CharZero K] in
/-- Powers of an element of the closed unit ball are no further from `1` than the element is:
`u ^ n - 1 = (u - 1) * ∑ l < n, u ^ l` and the sum has norm at most `1`. -/
theorem norm_pow_sub_one_le {u : K} (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  have h : u ^ n - 1 = (u - 1) * ∑ l ∈ Finset.range n, u ^ l := by rw [mul_comm, geom_sum_mul]
  rw [h, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ ↦ ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hu

omit [CompleteSpace K] [CharZero K] in
/-- A finite product of elements of the closed unit ball, each within `c` of `1`, is within `c`
of `1`. -/
theorem norm_prod_sub_one_le {ι : Type*} {s : Finset ι} {f : ι → K} {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (h : ∀ i ∈ s, ‖f i - 1‖ ≤ c) :
    ‖∏ i ∈ s, f i - 1‖ ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc
  | @insert a s ha ih =>
    have hprod : ‖∏ i ∈ s, f i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ ↦ norm_nonneg _)
        fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha]
    refine (norm_mul_sub_one_le_max hprod).trans (max_le (h a (Finset.mem_insert_self a s)) ?_)
    exact ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      fun i hi ↦ h i (Finset.mem_insert_of_mem hi)

omit [CompleteSpace K] [CharZero K] in
/-- `‖1/x - 1‖ = ‖(1 - x)/x‖ = ‖1 - x‖`. [Con, p. 27]. -/
theorem norm_inv_sub_one {u : K} (hu : ‖u - 1‖ < 1) : ‖u⁻¹ - 1‖ = ‖u - 1‖ := by
  have hu1 : ‖u‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu1
  have h : u⁻¹ - 1 = (1 - u) / u := by field_simp
  rw [h, norm_div, hu1, div_one, norm_sub_rev]

omit [CompleteSpace K] [CharZero K] in
theorem norm_pow_sub_one_lt {u : K} (hu : ‖u - 1‖ < 1) (n : ℕ) : ‖u ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact norm_mul_sub_one_lt ih hu

omit [CompleteSpace K] [CharZero K] in
theorem norm_zpow_sub_one_lt {u : K} (hu : ‖u - 1‖ < 1) (n : ℤ) : ‖u ^ n - 1‖ < 1 := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact norm_pow_sub_one_lt hu m
  · rw [zpow_neg, zpow_natCast, norm_inv_sub_one (norm_pow_sub_one_lt hu m)]
    exact norm_pow_sub_one_lt hu m

end OneUnits

/-! ### The logarithm on the full unit disc, for every prime `p` -/

section FullDisc

variable (h3 : ‖((p : ℕ) : K)‖ < 1)
include h3

omit h3 [IsUltrametricDist K] [CompleteSpace K] in
/-- The dominating sequence `r ^ (j+1) / ‖p‖ ^ v_p(j+1)` tends to `0` for `0 ≤ r < 1`:
`‖p‖ ^ v_p(j+1) ≥ ‖p‖ ^ log_p(j+1) ≥ (j+1)^(-k)` for a fixed `k` with `‖p‖⁻¹ ≤ p ^ k`, and
`r ^ (j+1) (j+1) ^ k → 0`. [Con, Example 3.10]. -/
theorem tendsto_pow_div_norm_pow_padicValNat {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Tendsto (fun j : ℕ => r ^ (j + 1) / ‖((p : ℕ) : K)‖ ^ padicValNat p (j + 1)) atTop (𝓝 0) := by
  have hp0 : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖((p : ℕ) : K)‖⁻¹) hp1
  have hbound : ∀ j : ℕ, r ^ (j + 1) / ‖((p : ℕ) : K)‖ ^ padicValNat p (j + 1)
      ≤ r ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ k := by
    intro j
    have hpv : (p : ℝ) ^ padicValNat p (j + 1) ≤ ((j + 1 : ℕ) : ℝ) := by
      have h1 : p ^ padicValNat p (j + 1) ≤ j + 1 :=
        calc p ^ padicValNat p (j + 1) ≤ p ^ Nat.log p (j + 1) :=
              Nat.pow_le_pow_right hp.out.pos (padicValNat_le_nat_log (j + 1))
          _ ≤ j + 1 := Nat.pow_log_le_self p (Nat.succ_ne_zero j)
      exact_mod_cast h1
    have hinv : (‖((p : ℕ) : K)‖ ^ padicValNat p (j + 1))⁻¹ ≤ ((j + 1 : ℕ) : ℝ) ^ k := by
      rw [← inv_pow]
      calc (‖((p : ℕ) : K)‖⁻¹) ^ padicValNat p (j + 1)
          ≤ ((p : ℝ) ^ k) ^ padicValNat p (j + 1) := pow_le_pow_left₀ (by positivity) hk.le _
        _ = ((p : ℝ) ^ padicValNat p (j + 1)) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ ((j + 1 : ℕ) : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hpv k
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (pow_nonneg hr0 _)
  have hlim : Tendsto (fun j : ℕ => r ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ k) atTop (𝓝 0) := by
    have := (tendsto_pow_const_mul_const_pow_of_lt_one k hr0 hr).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun j => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  exact squeeze_zero (fun j => by positivity) hbound hlim

omit [CompleteSpace K] [CharZero K] in
/-- The norm of the `n`-th term of the logarithm series. -/
theorem norm_padicLog_term_eq (u : K) (n : ℕ) :
    ‖(1 - u) ^ (n + 1) / ((n : K) + 1)‖ =
      ‖u - 1‖ ^ (n + 1) / ‖((p : ℕ) : K)‖ ^ padicValNat p (n + 1) := by
  have hcast : ((n : K) + 1) = ((n + 1 : ℕ) : K) := by push_cast; ring
  rw [norm_div, norm_pow, norm_sub_rev, hcast,
    norm_natCast_eq_pow_padicValNat h3 (Nat.succ_ne_zero n)]

/-- The logarithm series `∑ (1 - u)^(n+1) / (n+1)` converges on the whole open disc
`‖u - 1‖ < 1`, for every prime `p` [Con, Example 3.10 and Definition 8.1]. -/
theorem summable_padicLog_term {u : K} (hu : ‖u - 1‖ < 1) :
    Summable fun n : ℕ => (1 - u) ^ (n + 1) / ((n : K) + 1) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [(tendsto_pow_div_norm_pow_padicValNat (K := K) (p := p) (norm_nonneg _) hu).eventually
    (gt_mem_nhds hε)] with n hn
  rw [norm_padicLog_term_eq h3]
  exact hn

/-- **The logarithm as a limit** (Iwasawa): on the whole disc `‖u - 1‖ < 1` and for every prime
`p`, `log u = limₖ (u^(pᵏ) - 1)/pᵏ`.

The binomial expansion of `u^(pᵏ) - 1` has `j`-th coefficient
`C(pᵏ, j+1)/pᵏ = C(pᵏ - 1, j)/(j+1)`, which tends to `(-1)^j/(j+1)` because `pᵏ → 0` in
`K`; the uniform domination `‖(u-1)^(j+1) C(pᵏ, j+1)/pᵏ‖ ≤ ‖u-1‖^(j+1)/‖p‖^(v_p(j+1))` lets
one pass to the limit inside the sum. This description is the engine for the additivity of the
logarithm: it is visibly additive in `u`, which the series is not. -/
theorem tendsto_padicLog {u : K} (hu : ‖u - 1‖ < 1) :
    Tendsto (fun k : ℕ => (u ^ p ^ k - 1) / ((p : ℕ) : K) ^ k) atTop (𝓝 (padicLog u)) := by
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  set F : ℕ → ℕ → K := fun k j =>
    (u - 1) ^ (j + 1) * (((p ^ k).choose (j + 1) : ℕ) : K) / ((p : ℕ) : K) ^ k with hFdef
  set G : ℕ → K := fun j => (-1 : K) ^ j * (u - 1) ^ (j + 1) / ((j : K) + 1) with hGdef
  set B : ℕ → ℝ := fun j => ‖u - 1‖ ^ (j + 1) / ‖((p : ℕ) : K)‖ ^ padicValNat p (j + 1) with hBdef
  -- the shape of the terms after cancelling one power of `p`
  have hFalt : ∀ k j : ℕ,
      F k j = (u - 1) ^ (j + 1) * (((p ^ k - 1).choose j : ℕ) : K) / ((j : K) + 1) := by
    intro k j
    have hNpos : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
    have hj1 : ((j : K) + 1) ≠ 0 := by
      have : ((j : K) + 1) = ((j + 1 : ℕ) : K) := by push_cast; ring
      rw [this, Nat.cast_ne_zero]
      exact Nat.succ_ne_zero j
    have key : ((p : ℕ) : K) ^ k * (((p ^ k - 1).choose j : ℕ) : K)
        = (((p ^ k).choose (j + 1) : ℕ) : K) * ((j : K) + 1) := by
      have h := Nat.add_one_mul_choose_eq (p ^ k - 1) j
      rw [Nat.sub_add_cancel hNpos] at h
      have h' := congrArg (fun m : ℕ => (m : K)) h
      push_cast at h'
      exact h'
    simp only [hFdef]
    rw [div_eq_div_iff (pow_ne_zero _ h3ne) hj1]
    calc (u - 1) ^ (j + 1) * (((p ^ k).choose (j + 1) : ℕ) : K) * ((j : K) + 1)
        = (u - 1) ^ (j + 1) * ((((p ^ k).choose (j + 1) : ℕ) : K) * ((j : K) + 1)) := by ring
      _ = (u - 1) ^ (j + 1) * (((p : ℕ) : K) ^ k * (((p ^ k - 1).choose j : ℕ) : K)) := by rw [key]
      _ = (u - 1) ^ (j + 1) * (((p ^ k - 1).choose j : ℕ) : K) * ((p : ℕ) : K) ^ k := by ring
  -- the terms vanish beyond the binomial's range
  have hvanish : ∀ k : ℕ, ∀ j ∉ Finset.range (p ^ k), F k j = 0 := by
    intro k j hj
    rw [Finset.mem_range, not_lt] at hj
    have hz : (p ^ k).choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [hFdef, hz, Nat.cast_zero, mul_zero, zero_div]
  have hFsummable : ∀ k, Summable (F k) := fun k => summable_of_ne_finset_zero (hvanish k)
  -- the binomial expansion
  have hbin : ∀ N : ℕ, u ^ N - 1
      = ∑ j ∈ Finset.range N, (u - 1) ^ (j + 1) * ((N.choose (j + 1) : ℕ) : K) := by
    intro N
    have hpow : u ^ N = ((u - 1) + 1) ^ N := by ring
    rw [hpow, add_pow]
    simp only [one_pow, mul_one]
    rw [Finset.sum_range_succ']
    simp
  have hsum_eq : ∀ k : ℕ, (u ^ p ^ k - 1) / ((p : ℕ) : K) ^ k = ∑' j, F k j := by
    intro k
    rw [tsum_eq_sum (hvanish k), hbin, Finset.sum_div]
  -- the limit series is the logarithm
  have hterm : ∀ n : ℕ, -((1 - u) ^ (n + 1) / ((n : K) + 1)) = G n := by
    intro n
    have h1 : (1 : K) - u = -(u - 1) := by ring
    simp only [hGdef]
    rw [h1, neg_pow, pow_succ]
    ring
  have hlogeq : padicLog u = ∑' j, G j := by
    rw [padicLog, ← tsum_neg]
    exact tsum_congr hterm
  have hGsummable : Summable G := (summable_padicLog_term h3 hu).neg.congr hterm
  -- the uniform domination
  have hnormcast : ∀ j : ℕ, ‖((j : K) + 1)‖ = ‖((p : ℕ) : K)‖ ^ padicValNat p (j + 1) := by
    intro j
    have hcast : ((j : K) + 1) = ((j + 1 : ℕ) : K) := by push_cast; ring
    rw [hcast, norm_natCast_eq_pow_padicValNat h3 (Nat.succ_ne_zero j)]
  have hFB : ∀ k j, ‖F k j‖ ≤ B j := by
    intro k j
    rw [hFalt k j, norm_div, norm_mul, norm_pow, hnormcast]
    simp only [hBdef]
    gcongr
    exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one K _)
  have hGnorm : ∀ j, ‖G j‖ = B j := by
    intro j
    simp only [hGdef, hBdef, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      hnormcast]
  -- the domination tends to zero
  have hBtend : Tendsto B atTop (𝓝 0) :=
    tendsto_pow_div_norm_pow_padicValNat (norm_nonneg _) hu
  -- termwise convergence of the binomial coefficients
  have hchoose : ∀ j : ℕ,
      Tendsto (fun k : ℕ => (((p ^ k - 1).choose j : ℕ) : K)) atTop (𝓝 ((-1 : K) ^ j)) := by
    intro j
    have hfac : ((j ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hval := prod_range_neg_one_sub (K := K) j
    have hprod : Tendsto (fun k : ℕ => ∏ i ∈ Finset.range j, (((p : ℕ) : K) ^ k - 1 - (i : K)))
        atTop (𝓝 (∏ i ∈ Finset.range j, ((-1 : K) - (i : K)))) := by
      refine tendsto_finsetProd _ fun i _ => ?_
      have h0 : Tendsto (fun k : ℕ => ((p : ℕ) : K) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one h3
      have h1 := (h0.sub_const (1 : K)).sub_const (i : K)
      rwa [zero_sub] at h1
    have hprod' : Tendsto
        (fun k : ℕ => (∏ i ∈ Finset.range j, (((p : ℕ) : K) ^ k - 1 - (i : K))) / ((j ! : ℕ) : K))
        atTop (𝓝 ((-1 : K) ^ j)) := by
      have h := hprod.div_const ((j ! : ℕ) : K)
      rwa [hval, mul_div_assoc, div_self hfac, mul_one] at h
    refine hprod'.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop j] with k hk
    have hjk : j ≤ p ^ k - 1 := by
      have h1 : k < p ^ k := Nat.lt_pow_self hp.out.one_lt
      omega
    have h3sub : (((p ^ k - 1 : ℕ)) : K) = ((p : ℕ) : K) ^ k - 1 := by
      have h1 : (1 : ℕ) ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
      rw [Nat.cast_sub h1]
      push_cast
      ring
    have hc := cast_choose_mul_factorial (K := K) hjk
    rw [h3sub] at hc
    rw [← hc, mul_div_assoc, div_self hfac, mul_one]
  have hFlim : ∀ j, Tendsto (fun k => F k j) atTop (𝓝 (G j)) := by
    intro j
    have h := ((hchoose j).const_mul ((u - 1) ^ (j + 1))).div_const ((j : K) + 1)
    rw [show (u - 1) ^ (j + 1) * (-1 : K) ^ j = (-1 : K) ^ j * (u - 1) ^ (j + 1) from
      mul_comm _ _] at h
    simpa only [hFalt, hGdef] using h
  simp only [hsum_eq, hlogeq]
  exact tendsto_tsum_of_forall_norm_le hFsummable hGsummable hFB (fun j => (hGnorm j).le)
    hBtend hFlim

/-- `u^(pᵏ) → 1` for a `1`-unit `u`: `u^(pᵏ) - 1 = ((u^(pᵏ) - 1)/pᵏ) · pᵏ`. -/
theorem tendsto_pow_pow_sub_one {u : K} (hu : ‖u - 1‖ < 1) :
    Tendsto (fun k : ℕ => u ^ p ^ k - 1) atTop (𝓝 0) := by
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have h := (tendsto_padicLog h3 hu).mul (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h3)
  rw [mul_zero] at h
  refine h.congr fun k => ?_
  exact div_mul_cancel₀ _ (pow_ne_zero _ h3ne)

/-- The logarithm turns products of `1`-units into sums, on the whole disc and for every
prime `p` [Con, Theorem 8.5]. Proof via `tendsto_padicLog`:
`((uv)^(pᵏ) - 1)/pᵏ = (u^(pᵏ) - 1)/pᵏ + (v^(pᵏ) - 1)/pᵏ + ((u^(pᵏ) - 1)/pᵏ)·(v^(pᵏ) - 1)`, and the
last term tends to `log u · 0`. -/
theorem padicLog_mul {u v : K} (hu : ‖u - 1‖ < 1) (hv : ‖v - 1‖ < 1) :
    padicLog (u * v) = padicLog u + padicLog v := by
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hA := tendsto_padicLog h3 hu
  have hB := tendsto_padicLog h3 hv
  have hb0 := tendsto_pow_pow_sub_one h3 hv
  have huv := tendsto_padicLog h3 (norm_mul_sub_one_lt hu hv)
  have hsum := (hA.add hB).add (hA.mul hb0)
  rw [mul_zero, add_zero] at hsum
  refine tendsto_nhds_unique huv (hsum.congr fun k => ?_)
  have hpk : ((p : ℕ) : K) ^ k ≠ 0 := pow_ne_zero _ h3ne
  rw [mul_pow]
  field_simp
  ring

/-- [Con, Corollary 8.6]. -/
theorem padicLog_inv {u : K} (hu : ‖u - 1‖ < 1) : padicLog u⁻¹ = -padicLog u := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have h := padicLog_mul h3 hu (by rwa [norm_inv_sub_one hu])
  rw [mul_inv_cancel₀ hu0, padicLog_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- [Con, Corollary 8.6]. -/
theorem padicLog_pow {u : K} (hu : ‖u - 1‖ < 1) (n : ℕ) : padicLog (u ^ n) = n * padicLog u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicLog_mul h3 (norm_pow_sub_one_lt hu n) hu, ih, Nat.cast_succ]
    ring

/-- [Con, Corollary 8.6]. -/
theorem padicLog_zpow {u : K} (hu : ‖u - 1‖ < 1) (n : ℤ) :
    padicLog (u ^ n) = n * padicLog u := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, padicLog_pow h3 hu m, Int.cast_natCast]
  · rw [zpow_neg, zpow_natCast, padicLog_inv h3 (norm_pow_sub_one_lt hu m), padicLog_pow h3 hu m,
      Int.cast_neg, Int.cast_natCast]
    ring

end FullDisc

/-! ### The exponential, and the logarithm on the exponential's disc -/

section Exp

variable (h3 : ‖((p : ℕ) : K)‖ < 1)
include h3

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The exponential's disc `‖u - 1‖ ^ 2 < ‖p‖` lies inside the logarithm's disc `‖u - 1‖ < 1`. -/
theorem norm_sub_one_lt_one_of_sq_lt {u : K} (hu : ‖u - 1‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    ‖u - 1‖ < 1 :=
  lt_of_pow_lt_pow_left₀ 2 zero_le_one (by simpa using hu.trans h3)

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The isometry disc `‖u - 1‖ ^ (p - 1) < ‖p‖` of [Con, Theorem 8.7] lies inside the
logarithm's disc `‖u - 1‖ < 1`. -/
theorem norm_sub_one_lt_one_of_pow_lt {u : K} (hu : ‖u - 1‖ ^ (p - 1) < ‖((p : ℕ) : K)‖) :
    ‖u - 1‖ < 1 := by
  by_contra hcon
  exact absurd (one_le_pow₀ (not_lt.mp hcon)) (not_le.2 (hu.trans h3))

omit [CompleteSpace K] [CharZero K] in
/-- A natural number divisible by `p` has norm at most `‖p‖`. -/
theorem norm_natCast_le_of_dvd {n : ℕ} (hn : n ≠ 0) (hdvd : p ∣ n) :
    ‖(n : K)‖ ≤ ‖((p : ℕ) : K)‖ := by
  rw [norm_natCast_eq_pow_padicValNat h3 hn]
  calc ‖((p : ℕ) : K)‖ ^ padicValNat p n ≤ ‖((p : ℕ) : K)‖ ^ 1 :=
        pow_le_pow_of_le_one (norm_nonneg _) h3.le (one_le_padicValNat_of_dvd hn hdvd)
    _ = ‖((p : ℕ) : K)‖ := pow_one _

omit [CompleteSpace K] in
/-- Raising a `1`-unit to the `p`-th power multiplies its distance to `1` by exactly `‖p‖`, on
the disc `‖u - 1‖ ^ (p - 1) < ‖p‖` of [Con, Theorem 8.7]. Unlike `norm_pow_p_sub_one` this holds
for every prime, `p = 2` included.

Writing `z = u - 1`, the binomial expansion is `u ^ p - 1 = p * z + ∑_{2 ≤ k ≤ p} C(p, k) z ^ k`.
Every term of the sum is strictly smaller than `‖p‖ * ‖z‖`: for `k < p` because `p ∣ C(p, k)` and
`‖z‖ ^ k ≤ ‖z‖ ^ 2 < ‖z‖`, and for `k = p` because `‖z‖ ^ p = ‖z‖ ^ (p - 1) * ‖z‖ < ‖p‖ * ‖z‖`
is the hypothesis. -/
theorem norm_pow_p_sub_one' {u : K} (hu : ‖u - 1‖ ^ (p - 1) < ‖((p : ℕ) : K)‖) :
    ‖u ^ p - 1‖ = ‖((p : ℕ) : K)‖ * ‖u - 1‖ := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1 : p - 1 + 1 = p := by omega
  set z : K := u - 1 with hz
  rcases eq_or_ne z 0 with hz0 | hz0
  · have hu1 : u = 1 := by rwa [hz, sub_eq_zero] at hz0
    simp [hu1, hz]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hz1 : ‖z‖ < 1 := norm_sub_one_lt_one_of_pow_lt h3 hu
  -- The binomial expansion, with the constant and the linear term split off.
  set R : K := ∑ m ∈ Finset.Ico 2 (p + 1), z ^ m * (p.choose m : K) with hR
  have hexp : u ^ p - 1 = ((p : ℕ) : K) * z + R := by
    have huz : u = z + 1 := by rw [hz]; ring
    have hbin : (z + 1) ^ p = ∑ m ∈ Finset.range (p + 1), z ^ m * (p.choose m : K) := by
      rw [add_pow]
      exact Finset.sum_congr rfl fun m _ ↦ by rw [one_pow, mul_one]
    have hsplit : ∑ m ∈ Finset.range (p + 1), z ^ m * (p.choose m : K)
        = (∑ m ∈ Finset.range 2, z ^ m * (p.choose m : K)) + R := by
      rw [hR, Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le 2) (by omega)]
    rw [huz, hbin, hsplit, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_zero, pow_one,
      mul_one]
    ring
  -- Every term of `R` is at most `max (‖p‖ * ‖z‖ ^ 2) (‖z‖ ^ p)`.
  have hterm : ∀ m ∈ Finset.Ico 2 (p + 1),
      ‖z ^ m * (p.choose m : K)‖ ≤ max (‖((p : ℕ) : K)‖ * ‖z‖ ^ 2) (‖z‖ ^ p) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    rw [norm_mul, norm_pow]
    rcases eq_or_lt_of_le (show m ≤ p by omega) with heq | hlt
    · refine le_max_of_le_right ?_
      rw [heq, Nat.choose_self, Nat.cast_one, norm_one, mul_one]
    · refine le_max_of_le_left ?_
      have hne0 : p.choose m ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hnormle : ‖((p.choose m : ℕ) : K)‖ ≤ ‖((p : ℕ) : K)‖ :=
        norm_natCast_le_of_dvd h3 hne0 (Nat.Prime.dvd_choose_self hp.out (by omega) hlt)
      calc ‖z‖ ^ m * ‖((p.choose m : ℕ) : K)‖
          ≤ ‖z‖ ^ 2 * ‖((p : ℕ) : K)‖ :=
            mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hm.1) hnormle
              (norm_nonneg _) (by positivity)
        _ = ‖((p : ℕ) : K)‖ * ‖z‖ ^ 2 := mul_comm _ _
  have hRle : ‖R‖ ≤ max (‖((p : ℕ) : K)‖ * ‖z‖ ^ 2) (‖z‖ ^ p) :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (le_max_of_le_left (by positivity)) hterm
  have hmax : max (‖((p : ℕ) : K)‖ * ‖z‖ ^ 2) (‖z‖ ^ p) < ‖((p : ℕ) : K)‖ * ‖z‖ := by
    have hsq : ‖z‖ ^ 2 < ‖z‖ := by nlinarith
    refine max_lt (mul_lt_mul_of_pos_left hsq h3pos) ?_
    calc ‖z‖ ^ p = ‖z‖ ^ (p - 1) * ‖z‖ := by rw [← pow_succ, hp1]
      _ < ‖((p : ℕ) : K)‖ * ‖z‖ := by gcongr
  have hlt : ‖R‖ < ‖((p : ℕ) : K) * z‖ := by
    rw [norm_mul]
    exact hRle.trans_lt hmax
  rw [hexp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le,
    norm_mul]

omit [CompleteSpace K] in
/-- Norm bound for the logarithm on the small disc: if `‖u - 1‖ ≤ ‖p‖` then
`‖padicLog u‖ ≤ ‖p‖` (each term `(u-1)^(n+1)/(n+1)` has norm `≤ ‖p‖^(n+1) / ‖p‖^v_p(n+1)
≤ ‖p‖`). -/
theorem norm_padicLog_le {u : K} (hu : ‖u - 1‖ ≤ ‖((p : ℕ) : K)‖) :
    ‖padicLog u‖ ≤ ‖((p : ℕ) : K)‖ := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  rw [padicLog, norm_neg]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
  have hcast : ((n : K) + 1) = ((n + 1 : ℕ) : K) := by push_cast; ring
  have hrev : ‖(1 : K) - u‖ = ‖u - 1‖ := norm_sub_rev 1 u
  rw [norm_div, norm_pow, hrev, hcast,
    norm_natCast_eq_pow_padicValNat h3 (Nat.succ_ne_zero n), div_le_iff₀ (pow_pos h3pos _)]
  calc ‖u - 1‖ ^ (n + 1) ≤ ‖((p : ℕ) : K)‖ ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) hu (n + 1)
    _ = ‖((p : ℕ) : K)‖ * ‖((p : ℕ) : K)‖ ^ n := by ring
    _ ≤ ‖((p : ℕ) : K)‖ * ‖((p : ℕ) : K)‖ ^ padicValNat p (n + 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg _) h3.le (padicValNat_succ_le n))
          (norm_nonneg _)

omit [CompleteSpace K] in
/-- Every nonconstant term of the exponential series is bounded by `‖w‖` on the closed disc
`‖w‖² ≤ ‖p‖`: squaring, `‖w‖^(2m) ≤ ‖w‖² ‖p‖^(m-1) ≤ ‖w‖² ‖m !‖²` by `sq_norm_factorial_ge`. -/
theorem norm_padicExp_term_le (hp2 : p ≠ 2) {w : K} (hw : ‖w‖ ^ 2 ≤ ‖((p : ℕ) : K)‖) {m : ℕ}
    (hm : m ≠ 0) : ‖w ^ m / ((m ! : ℕ) : K)‖ ≤ ‖w‖ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hfac : (0 : ℝ) < ‖(((k + 1)! : ℕ) : K)‖ := by
    rw [norm_pos_iff, Nat.cast_ne_zero]
    exact Nat.factorial_ne_zero _
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _) ?_
  rw [norm_div, norm_pow, div_pow, div_le_iff₀ (pow_pos hfac 2)]
  calc (‖w‖ ^ (k + 1)) ^ 2 = ‖w‖ ^ 2 * (‖w‖ ^ 2) ^ k := by ring
    _ ≤ ‖w‖ ^ 2 * ‖((p : ℕ) : K)‖ ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hw k) (sq_nonneg _)
    _ ≤ ‖w‖ ^ 2 * ‖(((k + 1)! : ℕ) : K)‖ ^ 2 := by
        have h := sq_norm_factorial_ge h3 hp2 (n := k + 1) (Nat.succ_ne_zero k)
        simp only [Nat.add_sub_cancel] at h
        exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- The exponential series `∑ wⁿ / n !` converges on the open disc `‖w‖² < ‖p‖`: the squared
term norms are dominated by the geometric series of ratio `‖w‖² / ‖p‖ < 1`. -/
theorem summable_padicExp_term (hp2 : p ≠ 2) {w : K} (hw : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    Summable fun n : ℕ => w ^ n / ((n ! : ℕ) : K) := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  set q : ℝ := ‖w‖ ^ 2 / ‖((p : ℕ) : K)‖ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one h3pos).mpr hw
  have hbdd : ∀ k : ℕ, ‖w ^ (k + 1) / (((k + 1)! : ℕ) : K)‖ ^ 2 ≤ ‖w‖ ^ 2 * q ^ k := by
    intro k
    have hfac : ‖((p : ℕ) : K)‖ ^ k ≤ ‖(((k + 1)! : ℕ) : K)‖ ^ 2 := by
      have h := sq_norm_factorial_ge h3 hp2 (n := k + 1) (Nat.succ_ne_zero k)
      simp only [Nat.add_sub_cancel] at h
      exact h
    rw [norm_div, norm_pow, div_pow]
    calc (‖w‖ ^ (k + 1)) ^ 2 / ‖(((k + 1)! : ℕ) : K)‖ ^ 2
        ≤ (‖w‖ ^ (k + 1)) ^ 2 / ‖((p : ℕ) : K)‖ ^ k :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos h3pos k) hfac
      _ = ‖w‖ ^ 2 * q ^ k := by rw [hq, div_pow]; ring
  have hqt : Tendsto (fun k : ℕ => ‖w‖ ^ 2 * q ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (‖w‖ ^ 2)
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop, ← tendsto_add_atTop_iff_nat 1, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [hqt.eventually_lt_const (show (0 : ℝ) < ε ^ 2 by positivity)] with k hk
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (lt_of_le_of_lt (hbdd k) hk)

/-- On the exponential's disc (`‖w‖² < ‖p‖`, i.e. `v(w) > 1/2 ≥ 1/(p-1)` at odd `p`),
`‖padicExp w - 1‖ ≤ ‖w‖`: the linear term dominates. -/
theorem norm_padicExp_sub_one_le (hp2 : p ≠ 2) {w : K} (hw : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    ‖padicExp w - 1‖ ≤ ‖w‖ := by
  rw [padicExp, (summable_padicExp_term h3 hp2 hw).tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, add_sub_cancel_left]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le fun n =>
    norm_padicExp_term_le h3 hp2 hw.le (Nat.succ_ne_zero n)

omit [CompleteSpace K] in
/-- Squared bound for the `(k+1)`-st exponential term: `‖w^(k+1)/(k+1)!‖² ≤ ‖w‖² (‖w‖²/‖p‖)ᵏ`.
This is the engine behind both the convergence of the series and the second-order estimate
`norm_padicExp_sub_one_sub_self`. -/
private lemma sq_norm_padicExp_term_le (hp2 : p ≠ 2) (w : K) (k : ℕ) :
    ‖w ^ (k + 1) / (((k + 1)! : ℕ) : K)‖ ^ 2 ≤ ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖((p : ℕ) : K)‖) ^ k := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have hfac : ‖((p : ℕ) : K)‖ ^ k ≤ ‖(((k + 1)! : ℕ) : K)‖ ^ 2 := by
    have h := sq_norm_factorial_ge h3 hp2 (n := k + 1) (Nat.succ_ne_zero k)
    simpa using h
  rw [norm_div, norm_pow, div_pow]
  calc (‖w‖ ^ (k + 1)) ^ 2 / ‖(((k + 1)! : ℕ) : K)‖ ^ 2
      ≤ (‖w‖ ^ (k + 1)) ^ 2 / ‖((p : ℕ) : K)‖ ^ k :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos h3pos k) hfac
    _ = ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖((p : ℕ) : K)‖) ^ k := by rw [div_pow]; ring

omit [CompleteSpace K] in
/-- On the exponential's disc the *real* series of term norms converges: the terms are bounded
by the geometric progression `‖w‖ (‖w‖²/‖p‖)^(k/2)`.  This absolute convergence is what the
Cauchy product formula needs. -/
theorem summable_norm_padicExp_term (hp2 : p ≠ 2) {w : K} (hw : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    Summable fun n : ℕ => ‖w ^ n / ((n ! : ℕ) : K)‖ := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have hq0 : (0 : ℝ) ≤ ‖w‖ ^ 2 / ‖((p : ℕ) : K)‖ := by positivity
  have hq1 : ‖w‖ ^ 2 / ‖((p : ℕ) : K)‖ < 1 := (div_lt_one h3pos).mpr hw
  set r : ℝ := (1 + ‖w‖ ^ 2 / ‖((p : ℕ) : K)‖) / 2 with hrdef
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hrsq : ‖w‖ ^ 2 / ‖((p : ℕ) : K)‖ ≤ r ^ 2 := by
    rw [hrdef]; nlinarith [sq_nonneg (1 - ‖w‖ ^ 2 / ‖((p : ℕ) : K)‖)]
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left ‖w‖)
  refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero (by positivity) ?_
  calc ‖w ^ (k + 1) / (((k + 1)! : ℕ) : K)‖ ^ 2
      ≤ ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖((p : ℕ) : K)‖) ^ k := sq_norm_padicExp_term_le h3 hp2 w k
    _ ≤ ‖w‖ ^ 2 * (r ^ 2) ^ k := by gcongr
    _ = (‖w‖ * r ^ k) ^ 2 := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Additivity of the ultrametric exponential on its disc:
`exp (a + b) = exp a * exp b` for `‖a‖² < ‖p‖`, `‖b‖² < ‖p‖`.  (Cauchy product plus the
binomial theorem; [Kob84, Ch. IV §2].) -/
theorem padicExp_add (hp2 : p ≠ 2) {a b : K} (ha : ‖a‖ ^ 2 < ‖((p : ℕ) : K)‖)
    (hb : ‖b‖ ^ 2 < ‖((p : ℕ) : K)‖) : padicExp (a + b) = padicExp a * padicExp b := by
  have key : ∀ n : ℕ, ∑ kl ∈ Finset.antidiagonal n,
      a ^ kl.1 / ((kl.1 ! : ℕ) : K) * (b ^ kl.2 / ((kl.2 ! : ℕ) : K))
      = (a + b) ^ n / ((n ! : ℕ) : K) := by
    intro n
    rw [(Commute.all a b).add_pow' n, Finset.sum_div]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    obtain ⟨i, j⟩ := kl
    rw [Finset.mem_antidiagonal] at hkl
    subst hkl
    have hi : ((i ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hj : ((j ! : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hC : (((i + j).choose i : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right i j)).ne'
    have hcast : (((i + j).choose i : ℕ) : K) * ((i ! : ℕ) : K) * ((j ! : ℕ) : K)
        = (((i + j)! : ℕ) : K) := by
      have h : (i + j).choose i * i ! * j ! = (i + j)! := by
        rw [Nat.choose_symm_add]
        exact Nat.add_choose_mul_factorial_mul_factorial i j
      exact_mod_cast congrArg (fun m : ℕ => (m : K)) h
    rw [nsmul_eq_mul, ← hcast]
    field_simp
  rw [padicExp, padicExp, padicExp, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_padicExp_term h3 hp2 ha) (summable_norm_padicExp_term h3 hp2 hb)]
  exact (tsum_congr key).symm

/-- Second-order estimate for the exponential on its disc: `‖exp w - 1 - w‖ ≤ ‖w‖² / ‖p‖`.
(The quadratic term `w²/2` already has norm `≤ ‖w‖²`, and `‖p‖ ≤ 1` absorbs the `1/2`.) -/
theorem norm_padicExp_sub_one_sub_self (hp2 : p ≠ 2) {w : K} (hw : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    ‖padicExp w - 1 - w‖ ≤ ‖w‖ ^ 2 / ‖((p : ℕ) : K)‖ := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have hsum := summable_padicExp_term h3 hp2 hw
  have hs1 : Summable fun n : ℕ => w ^ (n + 1) / (((n + 1)! : ℕ) : K) :=
    (summable_nat_add_iff (f := fun n : ℕ => w ^ n / ((n ! : ℕ) : K)) 1).2 hsum
  have h1 : padicExp w - 1 - w = ∑' m : ℕ, w ^ (m + 1 + 1) / (((m + 1 + 1)! : ℕ) : K) := by
    have e1 : padicExp w = 1 + ∑' n : ℕ, w ^ (n + 1) / (((n + 1)! : ℕ) : K) := by
      rw [padicExp, hsum.tsum_eq_zero_add]
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have e2 : (∑' n : ℕ, w ^ (n + 1) / (((n + 1)! : ℕ) : K))
        = w + ∑' m : ℕ, w ^ (m + 1 + 1) / (((m + 1 + 1)! : ℕ) : K) := by
      rw [hs1.tsum_eq_zero_add]
      simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    rw [e1, e2]
    ring
  have hq0 : (0 : ℝ) ≤ ‖w‖ ^ 2 / ‖((p : ℕ) : K)‖ := by positivity
  have hq1 : ‖w‖ ^ 2 / ‖((p : ℕ) : K)‖ ≤ 1 := (div_le_one h3pos).2 hw.le
  rw [h1]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun m => ?_
  refine le_of_pow_le_pow_left₀ (n := 2) two_ne_zero (by positivity) ?_
  calc ‖w ^ (m + 1 + 1) / (((m + 1 + 1)! : ℕ) : K)‖ ^ 2
      ≤ ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖((p : ℕ) : K)‖) ^ (m + 1) := sq_norm_padicExp_term_le h3 hp2 w (m + 1)
    _ ≤ ‖w‖ ^ 2 * (‖w‖ ^ 2 / ‖((p : ℕ) : K)‖) ^ 1 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 (by omega)) (by positivity)
    _ = ‖w‖ ^ 4 / ‖((p : ℕ) : K)‖ := by ring
    _ ≤ ‖w‖ ^ 4 / ‖((p : ℕ) : K)‖ ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by nlinarith [norm_nonneg ((p : ℕ) : K), h3.le])
    _ = (‖w‖ ^ 2 / ‖((p : ℕ) : K)‖) ^ 2 := by rw [div_pow]; ring

omit [CompleteSpace K] in
/-- Raising a `1`-unit to the `p`-th power multiplies its distance to `1` by exactly
`‖p‖` (odd `p`).  Write `u^p − 1 = (u−1)·T` with `T = ∑_{i<p} uⁱ`; then
`T − p·1 = ∑_{i<p} (uⁱ − 1)` has norm `≤ ‖u−1‖`… refined: `T = (∑_{i<p} i)·(u−1) + p
+ (u−1)²·(integral)`, and `p ∣ ∑_{i<p} i` for odd `p`, so `‖T‖ = ‖p‖` on the disc. -/
theorem norm_pow_p_sub_one (hp2 : p ≠ 2) {u : K} (hu : ‖u - 1‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    ‖u ^ p - 1‖ = ‖((p : ℕ) : K)‖ * ‖u - 1‖ := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have hx1 : ‖u - 1‖ < 1 := lt_of_pow_lt_pow_left₀ 2 zero_le_one (by simpa using hu.trans h3)
  have hu1 : ‖u‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one hx1
  have hfact : u ^ p - 1 = (u - 1) * ∑ i ∈ Finset.range p, u ^ i := by
    rw [mul_comm, geom_sum_mul]
  have hpow_sub : ∀ j : ℕ, ‖u ^ j - 1‖ ≤ ‖u - 1‖ := by
    intro j
    have h1 : u ^ j - 1 = (u - 1) * ∑ l ∈ Finset.range j, u ^ l := by
      rw [mul_comm, geom_sum_mul]
    rw [h1, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => ?_
    rw [norm_pow, hu1, one_pow]
  -- `T = ∑ uⁱ`; the double-sum expansion `T − p = (u−1)·S`, `S := ∑_{i<p} ∑_{j<i} uʲ`
  have hTsub : (∑ i ∈ Finset.range p, u ^ i) - (p : K)
      = (u - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, u ^ j := by
    rw [Finset.mul_sum]
    have h1 : ∀ i ∈ Finset.range p, (u - 1) * ∑ j ∈ Finset.range i, u ^ j = u ^ i - 1 := by
      intro i _
      rw [mul_comm, geom_sum_mul]
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
    simp [Finset.card_range]
  -- `S − ∑_{i<p} i` has norm `≤ ‖u−1‖` (each `uʲ − 1` does)
  have hSsub : ‖(∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, u ^ j)
      - ((∑ i ∈ Finset.range p, i : ℕ) : K)‖ ≤ ‖u - 1‖ := by
    have h1 : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, u ^ j)
        - ((∑ i ∈ Finset.range p, i : ℕ) : K)
        = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (u ^ j - 1) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show ((i : K)) = ∑ _j ∈ Finset.range i, (1 : K) by simp,
        ← Finset.sum_sub_distrib]
    rw [h1]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
      fun i _ => ?_
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
      fun j _ => hpow_sub j
  -- `p ∣ ∑_{i<p} i` at odd `p`, so that term has norm `≤ ‖p‖`
  have hdvdN : ‖((∑ i ∈ Finset.range p, i : ℕ) : K)‖ ≤ ‖((p : ℕ) : K)‖ := by
    obtain ⟨t, ht⟩ : (p : ℕ) ∣ ∑ i ∈ Finset.range p, i := by
      have h2 : (∑ i ∈ Finset.range p, i) * 2 = p * (p - 1) := by
        rw [Finset.sum_range_id_mul_two]
      obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hp2
      refine ⟨m, Nat.eq_of_mul_eq_mul_right two_pos ?_⟩
      rw [h2, show p - 1 = 2 * m by omega]
      ring
    rw [ht]
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one K t)
  -- assemble: `‖T‖ = ‖p‖`
  have hT : ‖∑ i ∈ Finset.range p, u ^ i‖ = ‖((p : ℕ) : K)‖ := by
    have hkey : ‖(∑ i ∈ Finset.range p, u ^ i) - (p : K)‖ < ‖((p : ℕ) : K)‖ := by
      rw [hTsub, norm_mul]
      have hS : ‖∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, u ^ j‖
          ≤ max ‖u - 1‖ ‖((p : ℕ) : K)‖ := by
        have h1 := IsUltrametricDist.norm_add_le_max
          ((∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, u ^ j)
            - ((∑ i ∈ Finset.range p, i : ℕ) : K)) ((∑ i ∈ Finset.range p, i : ℕ) : K)
        simp only [sub_add_cancel] at h1
        exact h1.trans (max_le_max hSsub hdvdN)
      calc ‖u - 1‖ * ‖∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, u ^ j‖
          ≤ ‖u - 1‖ * max ‖u - 1‖ ‖((p : ℕ) : K)‖ :=
            mul_le_mul_of_nonneg_left hS (norm_nonneg _)
        _ < ‖((p : ℕ) : K)‖ := by
            rcases max_cases ‖u - 1‖ ‖((p : ℕ) : K)‖ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
            · calc ‖u - 1‖ * ‖u - 1‖ = ‖u - 1‖ ^ 2 := by ring
                _ < ‖((p : ℕ) : K)‖ := hu
            · calc ‖u - 1‖ * ‖((p : ℕ) : K)‖ < 1 * ‖((p : ℕ) : K)‖ :=
                  mul_lt_mul_of_pos_right hx1 h3pos
                _ = ‖((p : ℕ) : K)‖ := one_mul _
    have h2 : ∑ i ∈ Finset.range p, u ^ i
        = (p : K) + ((∑ i ∈ Finset.range p, u ^ i) - (p : K)) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hkey.ne',
      max_eq_left hkey.le]
  rw [hfact, norm_mul, hT, mul_comm]

omit [CompleteSpace K] in
/-- Iterating `norm_pow_p_sub_one'`: `‖u^(pᵏ) - 1‖ = ‖p‖^k ‖u - 1‖` on the isometry disc
`‖u - 1‖ ^ (p - 1) < ‖p‖`, for every prime `p`. This exact (not merely bounded) decay is
what makes the logarithm's limit description work. -/
theorem norm_pow_p_pow_sub_one' {u : K} (hu : ‖u - 1‖ ^ (p - 1) < ‖((p : ℕ) : K)‖) (k : ℕ) :
    ‖u ^ p ^ k - 1‖ = ‖((p : ℕ) : K)‖ ^ k * ‖u - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ‖u ^ p ^ k - 1‖ ^ (p - 1) < ‖((p : ℕ) : K)‖ := by
      rw [ih, mul_pow]
      calc (‖((p : ℕ) : K)‖ ^ k) ^ (p - 1) * ‖u - 1‖ ^ (p - 1)
          ≤ 1 * ‖u - 1‖ ^ (p - 1) := by
            gcongr
            exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) h3.le)
        _ = ‖u - 1‖ ^ (p - 1) := one_mul _
        _ < ‖((p : ℕ) : K)‖ := hu
    have hpow : u ^ p ^ (k + 1) = (u ^ p ^ k) ^ p := by rw [pow_succ, pow_mul]
    rw [hpow, norm_pow_p_sub_one' h3 hstep, ih, pow_succ]
    ring

omit [CompleteSpace K] in
theorem norm_pow_p_pow_sub_one (hp2 : p ≠ 2) {u : K}
    (hu : ‖u - 1‖ ^ 2 < ‖((p : ℕ) : K)‖) (k : ℕ) :
    ‖u ^ p ^ k - 1‖ = ‖((p : ℕ) : K)‖ ^ k * ‖u - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ‖u ^ p ^ k - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
      rw [ih, mul_pow]
      calc (‖((p : ℕ) : K)‖ ^ k) ^ 2 * ‖u - 1‖ ^ 2 ≤ 1 * ‖u - 1‖ ^ 2 := by
            gcongr
            exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) h3.le)
        _ = ‖u - 1‖ ^ 2 := one_mul _
        _ < ‖((p : ℕ) : K)‖ := hu
    have hpow : u ^ p ^ (k + 1) = (u ^ p ^ k) ^ p := by rw [pow_succ, pow_mul]
    rw [hpow, norm_pow_p_sub_one h3 hp2 hstep, ih, pow_succ]
    ring

/-- `exp (n·w) = (exp w)ⁿ` on the disc, by iterated additivity. -/
theorem padicExp_natCast_mul (hp2 : p ≠ 2) {w : K} (hw : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖)
    (n : ℕ) : padicExp ((n : K) * w) = padicExp w ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : ‖(n : K) * w‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
      rw [norm_mul, mul_pow]
      calc ‖(n : K)‖ ^ 2 * ‖w‖ ^ 2 ≤ 1 * ‖w‖ ^ 2 := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K n)
        _ = ‖w‖ ^ 2 := one_mul _
        _ < ‖((p : ℕ) : K)‖ := hw
    rw [show ((n + 1 : ℕ) : K) * w = (n : K) * w + w by push_cast; ring,
      padicExp_add h3 hp2 hn hw, ih, pow_succ]

/-- `exp` intertwines `pᵏ ·` with `(·)^(pᵏ)`. -/
theorem padicExp_pow_p_pow (hp2 : p ≠ 2) {w : K} (hw : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖)
    (k : ℕ) : padicExp w ^ p ^ k = padicExp (((p : ℕ) : K) ^ k * w) := by
  rw [show (((p : ℕ) : K)) ^ k * w = ((p ^ k : ℕ) : K) * w by push_cast; ring,
    padicExp_natCast_mul h3 hp2 hw (p ^ k)]

/-- **The logarithm is an isometry near `1`** [Con, Theorem 8.7]: `‖log u‖ = ‖u - 1‖` on the
disc `‖u - 1‖ ^ (p - 1) < ‖p‖`, for every prime `p`. Every term of the approximating sequence
of `tendsto_padicLog` has norm exactly `‖u - 1‖` by `norm_pow_p_pow_sub_one'`. -/
theorem norm_padicLog_eq' {u : K} (hu : ‖u - 1‖ ^ (p - 1) < ‖((p : ℕ) : K)‖) :
    ‖padicLog u‖ = ‖u - 1‖ := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have h := (tendsto_padicLog h3 (norm_sub_one_lt_one_of_pow_lt h3 hu)).norm
  have hconst : (fun k : ℕ => ‖(u ^ p ^ k - 1) / ((p : ℕ) : K) ^ k‖) = fun _ : ℕ => ‖u - 1‖ := by
    funext k
    rw [norm_div, norm_pow, norm_pow_p_pow_sub_one' h3 hu k,
      mul_div_cancel_left₀ _ (ne_of_gt (pow_pos h3pos k))]
  rw [hconst] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Sharp norm of the logarithm: `‖log u‖ = ‖u - 1‖` on the disc.  Every term of the
approximating sequence of `tendsto_padicLog` has norm exactly `‖u - 1‖`. -/
theorem norm_padicLog_eq (hp2 : p ≠ 2) {u : K} (hu : ‖u - 1‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    ‖padicLog u‖ = ‖u - 1‖ := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have h := (tendsto_padicLog h3 (norm_sub_one_lt_one_of_sq_lt h3 hu)).norm
  have hconst : (fun k : ℕ => ‖(u ^ p ^ k - 1) / ((p : ℕ) : K) ^ k‖) = fun _ : ℕ => ‖u - 1‖ := by
    funext k
    rw [norm_div, norm_pow, norm_pow_p_pow_sub_one h3 hp2 hu k,
      mul_div_cancel_left₀ _ (ne_of_gt (pow_pos h3pos k))]
  rw [hconst] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The logarithm is injective on the disc `‖u - 1‖² < ‖p‖`: the approximating sequences of
`u` and `v` differ by `v^(pᵏ)((u/v)^(pᵏ) - 1)/pᵏ`, whose norm is the constant `‖u - v‖`. -/
theorem eq_of_padicLog_eq (hp2 : p ≠ 2) {u v : K} (hu : ‖u - 1‖ ^ 2 < ‖((p : ℕ) : K)‖)
    (hv : ‖v - 1‖ ^ 2 < ‖((p : ℕ) : K)‖) (h : padicLog u = padicLog v) : u = v := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hv1 : ‖v - 1‖ < 1 := lt_of_pow_lt_pow_left₀ 2 zero_le_one (by simpa using hv.trans h3)
  have hvnorm : ‖v‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one hv1
  have hv0 : v ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hvnorm
    exact zero_ne_one hvnorm
  have hquot : ‖u / v - 1‖ = ‖u - v‖ := by rw [div_sub_one hv0, norm_div, hvnorm, div_one]
  have hdisc : ‖u / v - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [hquot]
    have hmax : ‖u - v‖ ≤ max ‖u - 1‖ ‖v - 1‖ := by
      calc ‖u - v‖ = ‖(u - 1) + -(v - 1)‖ := by congr 1; ring
        _ ≤ max ‖u - 1‖ ‖-(v - 1)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖u - 1‖ ‖v - 1‖ := by rw [norm_neg]
    rcases max_cases ‖u - 1‖ ‖v - 1‖ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hmax
    · exact lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hmax 2) hu
    · exact lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) hmax 2) hv
  have hkey := (tendsto_padicLog h3 (norm_sub_one_lt_one_of_sq_lt h3 hu)).sub (tendsto_padicLog h3 (norm_sub_one_lt_one_of_sq_lt h3 hv))
  rw [h, sub_self] at hkey
  have hnorm : ∀ k : ℕ,
      ‖(u ^ p ^ k - 1) / ((p : ℕ) : K) ^ k - (v ^ p ^ k - 1) / ((p : ℕ) : K) ^ k‖ = ‖u - v‖ := by
    intro k
    have hdiff : (u ^ p ^ k - 1) / ((p : ℕ) : K) ^ k - (v ^ p ^ k - 1) / ((p : ℕ) : K) ^ k
        = v ^ p ^ k * ((u / v) ^ p ^ k - 1) / ((p : ℕ) : K) ^ k := by
      rw [div_pow]
      field_simp
      ring
    rw [hdiff, norm_div, norm_mul, norm_pow, norm_pow, hvnorm, one_pow, one_mul,
      norm_pow_p_pow_sub_one h3 hp2 hdisc k, hquot,
      mul_div_cancel_left₀ _ (ne_of_gt (pow_pos h3pos k))]
  have hlim : Tendsto (fun _ : ℕ => ‖u - v‖) atTop (𝓝 0) := by
    have hn := hkey.norm
    simpa [hnorm] using hn
  have hzero : ‖u - v‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact sub_eq_zero.1 (norm_eq_zero.1 hzero)

/-- `log (exp w) = w` on the exponential's disc: by `padicExp_pow_p_pow` the approximating
sequence of `exp w` is `(exp (pᵏ w) - 1)/pᵏ = w + O(‖p‖^k)`. -/
theorem padicLog_padicExp (hp2 : p ≠ 2) {w : K} (hw : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    padicLog (padicExp w) = w := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hdisc : ‖padicExp w - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) (norm_padicExp_sub_one_le h3 hp2 hw) 2) hw
  have hstep : ∀ k : ℕ, ‖(padicExp w ^ p ^ k - 1) / ((p : ℕ) : K) ^ k - w‖
      ≤ ‖((p : ℕ) : K)‖ ^ k * (‖w‖ ^ 2 / ‖((p : ℕ) : K)‖) := by
    intro k
    have hk : ‖((p : ℕ) : K) ^ k * w‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
      rw [norm_mul, norm_pow, mul_pow]
      calc (‖((p : ℕ) : K)‖ ^ k) ^ 2 * ‖w‖ ^ 2 ≤ 1 * ‖w‖ ^ 2 := by
            gcongr
            exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) h3.le)
        _ = ‖w‖ ^ 2 := one_mul _
        _ < ‖((p : ℕ) : K)‖ := hw
    have hid : (padicExp w ^ p ^ k - 1) / ((p : ℕ) : K) ^ k - w
        = (padicExp (((p : ℕ) : K) ^ k * w) - 1 - ((p : ℕ) : K) ^ k * w) / ((p : ℕ) : K) ^ k := by
      rw [padicExp_pow_p_pow h3 hp2 hw k]
      field_simp
    rw [hid, norm_div, norm_pow, div_le_iff₀ (by positivity)]
    calc ‖padicExp (((p : ℕ) : K) ^ k * w) - 1 - ((p : ℕ) : K) ^ k * w‖
        ≤ ‖((p : ℕ) : K) ^ k * w‖ ^ 2 / ‖((p : ℕ) : K)‖ := norm_padicExp_sub_one_sub_self h3 hp2 hk
      _ = ‖((p : ℕ) : K)‖ ^ k * (‖w‖ ^ 2 / ‖((p : ℕ) : K)‖) * ‖((p : ℕ) : K)‖ ^ k := by
          rw [norm_mul, norm_pow, mul_pow]
          ring
  refine tendsto_nhds_unique (tendsto_padicLog h3 (norm_sub_one_lt_one_of_sq_lt h3 hdisc)) ?_
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm hstep ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h3).mul_const
    (‖w‖ ^ 2 / ‖((p : ℕ) : K)‖)

/-- `exp (log u) = u` on the joint disc `‖u - 1‖² < ‖p‖`.  [Kob84, Ch. IV §2,
Proposition]. -/
theorem padicExp_padicLog (hp2 : p ≠ 2) {u : K} (hu : ‖u - 1‖ ^ 2 < ‖((p : ℕ) : K)‖) :
    padicExp (padicLog u) = u := by
  have hL : ‖padicLog u‖ ^ 2 < ‖((p : ℕ) : K)‖ := by rw [norm_padicLog_eq h3 hp2 hu]; exact hu
  have hE : ‖padicExp (padicLog u) - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ :=
    lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _) (norm_padicExp_sub_one_le h3 hp2 hL) 2) hL
  exact eq_of_padicLog_eq h3 hp2 hE hu (padicLog_padicExp h3 hp2 hL)

end Exp

/-! ### The Iwasawa logarithm: extension to units, and to `K^×` with `log p = 0` -/

section Iwasawa

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `HasPrincipalUnitPow u` says that some positive power of `u` is a `1`-unit, `‖u ^ m - 1‖ < 1`.
In a field whose residue field is algebraic over `𝔽_p` (finite extensions of `ℚ_p`, `ℚ_p`-bar,
`ℂ_p`) this is every unit of the valuation ring (`PadicComplex.hasPrincipalUnitPow_of_norm_eq_one`). -/
def HasPrincipalUnitPow (u : K) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ‖u ^ m - 1‖ < 1

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
variable (p) in
/-- `HasIwasawaLog p x` says that some positive power of `x` is a `1`-unit times a power of `p`:
`‖x ^ N / p ^ m - 1‖ < 1` for some `N ≥ 1` and `m : ℤ`. This is the domain of the Iwasawa
logarithm; in `ℂ_p` it is all of `ℂ_p^×` (`PadicComplex.hasIwasawaLog_iff`) [Wiki]: "every element
w of C×_p can be written as w = p^r · ζ · z with r a rational number, ζ a root of unity, and
|z−1|_p < 1". -/
def HasIwasawaLog (x : K) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ m : ℤ, ‖x ^ N / ((p : ℕ) : K) ^ m - 1‖ < 1

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
variable (p) in
/-- The **Iwasawa logarithm**: the unique extension of `padicLog` from the `1`-units to
`HasIwasawaLog p` (all of `ℂ_p^×` when `K = ℂ_p`) which is a homomorphism and has `log p = 0`
[Wiki]. Concretely `iwasawaLog p x = padicLog (x ^ N / p ^ m) / N` for any `N ≥ 1`, `m` with
`‖x ^ N / p ^ m - 1‖ < 1` (independent of the choice by `iwasawaLog_eq_div`); junk value `0`
outside the domain. -/
noncomputable def iwasawaLog (x : K) : K := by
  classical
  exact if h : ∃ N : ℕ, 0 < N ∧ ∃ m : ℤ, ‖x ^ N / ((p : ℕ) : K) ^ m - 1‖ < 1 then
    padicLog (x ^ Nat.find h / ((p : ℕ) : K) ^ Classical.choose (Nat.find_spec h).2) /
      (Nat.find h : K)
  else 0

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem HasPrincipalUnitPow.of_norm_sub_one_lt {u : K} (hu : ‖u - 1‖ < 1) :
    HasPrincipalUnitPow u := by
  exact ⟨1, one_pos, by simpa using hu⟩

omit [CompleteSpace K] [CharZero K] in
theorem HasPrincipalUnitPow.mul {u v : K} (hu : HasPrincipalUnitPow u)
    (hv : HasPrincipalUnitPow v) : HasPrincipalUnitPow (u * v) := by
  obtain ⟨m, hm, h⟩ := hu
  obtain ⟨m', hm', h'⟩ := hv
  refine ⟨m * m', Nat.mul_pos hm hm', ?_⟩
  have e : (u * v) ^ (m * m') = (u ^ m) ^ m' * (v ^ m') ^ m := by
    rw [mul_pow, pow_mul, pow_mul']
  rw [e]
  exact norm_mul_sub_one_lt (norm_pow_sub_one_lt h m') (norm_pow_sub_one_lt h' m)

omit [CompleteSpace K] [CharZero K] in
theorem HasPrincipalUnitPow.inv {u : K} (hu : HasPrincipalUnitPow u) :
    HasPrincipalUnitPow u⁻¹ := by
  obtain ⟨m, hm, h⟩ := hu
  refine ⟨m, hm, ?_⟩
  rw [inv_pow, norm_inv_sub_one h]
  exact h

omit [CompleteSpace K] [CharZero K] in
theorem HasPrincipalUnitPow.pow {u : K} (hu : HasPrincipalUnitPow u) (n : ℕ) :
    HasPrincipalUnitPow (u ^ n) := by
  obtain ⟨m, hm, h⟩ := hu
  refine ⟨m, hm, ?_⟩
  rw [← pow_mul, pow_mul']
  exact norm_pow_sub_one_lt h n

omit [CompleteSpace K] [CharZero K] in
theorem HasPrincipalUnitPow.norm_eq_one {u : K} (hu : HasPrincipalUnitPow u) : ‖u‖ = 1 := by
  obtain ⟨m, hm, h⟩ := hu
  have h1 := norm_eq_one_of_norm_sub_one_lt_one h
  rw [norm_pow] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h1

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem HasPrincipalUnitPow.hasIwasawaLog {u : K} (hu : HasPrincipalUnitPow u) :
    HasIwasawaLog p u := by
  obtain ⟨m, hm, h⟩ := hu
  exact ⟨m, hm, 0, by simpa using h⟩

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem HasIwasawaLog.of_norm_sub_one_lt {u : K} (hu : ‖u - 1‖ < 1) : HasIwasawaLog p u := by
  exact ⟨1, one_pos, 0, by simpa using hu⟩

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem HasIwasawaLog.natCast_p : HasIwasawaLog p ((p : ℕ) : K) := by
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  exact ⟨1, one_pos, 1, by simp [h3ne]⟩

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem HasIwasawaLog.ne_zero {x : K} (hx : HasIwasawaLog p x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨N, hN, m, h⟩ := hx
  rw [zero_pow hN.ne', zero_div, zero_sub, norm_neg, norm_one] at h
  exact lt_irrefl _ h

omit [CompleteSpace K] in
theorem HasIwasawaLog.mul {x y : K} (hx : HasIwasawaLog p x) (hy : HasIwasawaLog p y) :
    HasIwasawaLog p (x * y) := by
  obtain ⟨N, hN, m, h⟩ := hx
  obtain ⟨N', hN', m', h'⟩ := hy
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  refine ⟨N * N', Nat.mul_pos hN hN', m * N' + m' * N, ?_⟩
  have e : (x * y) ^ (N * N') / ((p : ℕ) : K) ^ (m * N' + m' * N)
      = (x ^ N / ((p : ℕ) : K) ^ m) ^ N' * (y ^ N' / ((p : ℕ) : K) ^ m') ^ N := by
    rw [div_pow, div_pow, ← zpow_natCast (((p : ℕ) : K) ^ m), ← zpow_natCast (((p : ℕ) : K) ^ m'),
      ← zpow_mul, ← zpow_mul, div_mul_div_comm, ← zpow_add₀ h3ne, mul_pow, pow_mul, pow_mul']
  rw [e]
  exact norm_mul_sub_one_lt (norm_pow_sub_one_lt h N') (norm_pow_sub_one_lt h' N)

omit hp [CompleteSpace K] [CharZero K] in
theorem HasIwasawaLog.inv {x : K} (hx : HasIwasawaLog p x) : HasIwasawaLog p x⁻¹ := by
  obtain ⟨N, hN, m, h⟩ := hx
  refine ⟨N, hN, -m, ?_⟩
  rw [inv_pow, zpow_neg, inv_div_inv, ← inv_div (x ^ N), norm_inv_sub_one h]
  exact h

omit hp [CompleteSpace K] [CharZero K] in
theorem HasIwasawaLog.pow {x : K} (hx : HasIwasawaLog p x) (n : ℕ) : HasIwasawaLog p (x ^ n) := by
  obtain ⟨N, hN, m, h⟩ := hx
  refine ⟨N, hN, m * n, ?_⟩
  have e : (x ^ n) ^ N / ((p : ℕ) : K) ^ (m * n) = (x ^ N / ((p : ℕ) : K) ^ m) ^ n := by
    rw [div_pow, ← pow_mul, ← pow_mul, mul_comm n N, zpow_mul, zpow_natCast]
  rw [e]
  exact norm_pow_sub_one_lt h n

omit hp [CompleteSpace K] [CharZero K] in
theorem HasIwasawaLog.zpow {x : K} (hx : HasIwasawaLog p x) (n : ℤ) :
    HasIwasawaLog p (x ^ n) := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast]
    exact hx.pow k
  · rw [zpow_neg, zpow_natCast]
    exact (hx.pow k).inv

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `HasIwasawaLog` is transported along norm-preserving ring homomorphisms (e.g. `ℚ_p`-bar → `ℂ_p`). -/
theorem HasIwasawaLog.map {L : Type*} [NontriviallyNormedField L] (f : K →+* L)
    (hf : ∀ y : K, ‖f y‖ = ‖y‖) {x : K} (hx : HasIwasawaLog p x) : HasIwasawaLog p (f x) := by
  obtain ⟨N, hN, m, h⟩ := hx
  refine ⟨N, hN, m, ?_⟩
  rw [← map_natCast f, ← map_zpow₀, ← map_pow, ← map_div₀, ← map_one f, ← map_sub, hf]
  exact h

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `HasPrincipalUnitPow` is transported along norm-preserving ring homomorphisms. -/
theorem HasPrincipalUnitPow.map {L : Type*} [NontriviallyNormedField L] (f : K →+* L)
    (hf : ∀ y : K, ‖f y‖ = ‖y‖) {u : K} (hu : HasPrincipalUnitPow u) : HasPrincipalUnitPow (f u) := by
  obtain ⟨m, hm, h⟩ := hu
  refine ⟨m, hm, ?_⟩
  rw [← map_pow, ← map_one f, ← map_sub, hf]
  exact h

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem HasIwasawaLog.one : HasIwasawaLog p (1 : K) := .of_norm_sub_one_lt (by simp)

omit [CompleteSpace K] in
/-- A finite product of elements with an Iwasawa logarithm has an Iwasawa logarithm. -/
theorem HasIwasawaLog.prod {ι : Type*} {s : Finset ι} {f : ι → K}
    (hf : ∀ i ∈ s, HasIwasawaLog p (f i)) : HasIwasawaLog p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasIwasawaLog.one (p := p) (K := K)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

variable (h3 : ‖((p : ℕ) : K)‖ < 1)
include h3

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `‖p ^ j‖ = 1` forces `j = 0`, since `‖p‖ < 1`. -/
theorem zpow_natCast_p_eq_one_of_norm_eq_one {j : ℤ} (hj : ‖((p : ℕ) : K) ^ j‖ = 1) : j = 0 := by
  have hp0 : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  rw [norm_zpow] at hj
  exact zpow_right_injective₀ hp0 h3.ne (hj.trans (zpow_zero _).symm)

omit [CompleteSpace K] in
/-- Two `1`-units differing by a power of `p` are equal. -/
theorem eq_of_mul_zpow_natCast_p {a b : K} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) {j : ℤ}
    (h : a = b * ((p : ℕ) : K) ^ j) : a = b := by
  have ha1 := norm_eq_one_of_norm_sub_one_lt_one ha
  have hb1 := norm_eq_one_of_norm_sub_one_lt_one hb
  have hj : ‖((p : ℕ) : K) ^ j‖ = 1 := by
    have := congrArg norm h
    rw [norm_mul, ha1, hb1, one_mul] at this
    exact this.symm
  rw [h, zpow_natCast_p_eq_one_of_norm_eq_one h3 hj, zpow_zero, mul_one]

/-- `iwasawaLog p x = log (x ^ N / p ^ m) / N` for **every** admissible pair `(N, m)`. -/
theorem iwasawaLog_eq_div {x : K} {N : ℕ} (hN : 0 < N) {m : ℤ}
    (h : ‖x ^ N / ((p : ℕ) : K) ^ m - 1‖ < 1) :
    iwasawaLog p x = padicLog (x ^ N / ((p : ℕ) : K) ^ m) / N := by
  classical
  have hex : ∃ N : ℕ, 0 < N ∧ ∃ m : ℤ, ‖x ^ N / ((p : ℕ) : K) ^ m - 1‖ < 1 := ⟨N, hN, m, h⟩
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  unfold iwasawaLog
  rw [dif_pos hex]
  obtain ⟨hN₀, hm₀⟩ := Nat.find_spec hex
  have h₀ : ‖x ^ Nat.find hex / ((p : ℕ) : K) ^ Classical.choose hm₀ - 1‖ < 1 :=
    Classical.choose_spec hm₀
  set N₀ := Nat.find hex with hN₀def
  set m₀ := Classical.choose hm₀ with hm₀def
  set a := x ^ N / ((p : ℕ) : K) ^ m with hadef
  set b := x ^ N₀ / ((p : ℕ) : K) ^ m₀ with hbdef
  have hpm₀ : ((p : ℕ) : K) ^ m₀ ≠ 0 := zpow_ne_zero _ h3ne
  have hab : a ^ N₀ = b ^ N * ((p : ℕ) : K) ^ (m₀ * N - m * N₀) := by
    rw [zpow_sub₀ h3ne, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    simp only [hadef, hbdef, div_pow, ← pow_mul, mul_comm N₀ N]
    rw [div_mul_div_comm, mul_comm (x ^ (N * N₀)), mul_div_mul_left _ _ (pow_ne_zero _ hpm₀)]
  have key : (N₀ : K) * padicLog a = (N : K) * padicLog b := by
    rw [← padicLog_pow h3 h N₀, ← padicLog_pow h3 h₀ N,
      eq_of_mul_zpow_natCast_p h3 (norm_pow_sub_one_lt h N₀) (norm_pow_sub_one_lt h₀ N) hab]
  rw [div_eq_div_iff (Nat.cast_ne_zero.2 hN₀.ne') (Nat.cast_ne_zero.2 hN.ne'),
    mul_comm (padicLog b), mul_comm (padicLog a)]
  exact key.symm

theorem iwasawaLog_of_norm_sub_one_lt {x : K} (hx : ‖x - 1‖ < 1) :
    iwasawaLog p x = padicLog x := by
  rw [iwasawaLog_eq_div h3 one_pos (m := 0) (by simpa using hx)]
  simp

/-- The Iwasawa logarithm is continuous at `1` along any filter: if `u i → 1` then
`log_p (u i) → 0`. Near `1` the Iwasawa logarithm agrees with `padicLog`, which is an isometry
on the disc `‖u - 1‖ ^ (p - 1) < ‖p‖` (`norm_padicLog_eq'`), so `‖log_p (u i)‖ = ‖u i - 1‖`
eventually. -/
theorem tendsto_iwasawaLog_of_tendsto_one {ι : Type*} {l : Filter ι} {u : ι → K}
    (hu : Tendsto u l (𝓝 1)) : Tendsto (fun i ↦ iwasawaLog p (u i)) l (𝓝 0) := by
  have h3pos : (0 : ℝ) < ‖((p : ℕ) : K)‖ := norm_natCast_p_pos
  have hnorm : Tendsto (fun i ↦ ‖u i - 1‖) l (𝓝 0) := by
    simpa using (hu.sub_const 1).norm
  have hsmall : ∀ᶠ i in l, ‖u i - 1‖ ^ (p - 1) < ‖((p : ℕ) : K)‖ := by
    filter_upwards [hnorm.eventually (eventually_lt_nhds h3pos)] with i hi
    have hi0 : ‖u i - 1‖ < ‖((p : ℕ) : K)‖ := by simpa using hi
    calc ‖u i - 1‖ ^ (p - 1) ≤ ‖u i - 1‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) (hi0.le.trans h3.le)
            (Nat.one_le_iff_ne_zero.2 (by have := hp.out.two_le; omega))
      _ = ‖u i - 1‖ := pow_one _
      _ < ‖((p : ℕ) : K)‖ := hi0
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [hsmall, hnorm.eventually (eventually_lt_nhds hε)] with i hi hlt
  rw [iwasawaLog_of_norm_sub_one_lt h3 (norm_sub_one_lt_one_of_pow_lt h3 hi),
    norm_padicLog_eq' h3 hi]
  simpa using hlt

/-- On units with a `1`-unit power `x ^ m`, the Iwasawa logarithm is `log (x ^ m) / m`. -/
theorem iwasawaLog_of_hasPrincipalUnitPow {x : K} {m : ℕ} (hm : 0 < m) (hx : ‖x ^ m - 1‖ < 1) :
    iwasawaLog p x = padicLog (x ^ m) / m := by
  rw [iwasawaLog_eq_div h3 hm (m := 0) (by simpa using hx)]
  simp

omit hp h3 [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem iwasawaLog_of_not {x : K} (hx : ¬ HasIwasawaLog p x) : iwasawaLog p x = 0 := by
  classical
  unfold iwasawaLog
  exact dif_neg hx

omit hp h3 [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
@[simp] theorem iwasawaLog_zero : iwasawaLog p (0 : K) = 0 := by
  exact iwasawaLog_of_not fun h => h.ne_zero rfl

@[simp] theorem iwasawaLog_one : iwasawaLog p (1 : K) = 0 := by
  rw [iwasawaLog_of_norm_sub_one_lt h3 (by simp), padicLog_one]

/-- The normalisation `log p = 0` of the Iwasawa logarithm [Wiki]. -/
@[simp] theorem iwasawaLog_natCast_p : iwasawaLog p ((p : ℕ) : K) = 0 := by
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  rw [iwasawaLog_eq_div h3 one_pos (m := 1) (by simp [h3ne])]
  simp [h3ne]

theorem iwasawaLog_mul {x y : K} (hx : HasIwasawaLog p x) (hy : HasIwasawaLog p y) :
    iwasawaLog p (x * y) = iwasawaLog p x + iwasawaLog p y := by
  obtain ⟨N, hN, m, h⟩ := hx
  obtain ⟨N', hN', m', h'⟩ := hy
  have h3ne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hNN : 0 < N * N' := Nat.mul_pos hN hN'
  have hx' : ‖x ^ (N * N') / ((p : ℕ) : K) ^ (m * N') - 1‖ < 1 := by
    have e : x ^ (N * N') / ((p : ℕ) : K) ^ (m * N') = (x ^ N / ((p : ℕ) : K) ^ m) ^ N' := by
      rw [div_pow, ← pow_mul, zpow_mul, zpow_natCast]
    rw [e]
    exact norm_pow_sub_one_lt h N'
  have hy' : ‖y ^ (N * N') / ((p : ℕ) : K) ^ (m' * N) - 1‖ < 1 := by
    have e : y ^ (N * N') / ((p : ℕ) : K) ^ (m' * N) = (y ^ N' / ((p : ℕ) : K) ^ m') ^ N := by
      rw [div_pow, ← pow_mul, mul_comm N' N, zpow_mul, zpow_natCast]
    rw [e]
    exact norm_pow_sub_one_lt h' N
  have hxy : (x * y) ^ (N * N') / ((p : ℕ) : K) ^ (m * N' + m' * N)
      = x ^ (N * N') / ((p : ℕ) : K) ^ (m * N') * (y ^ (N * N') / ((p : ℕ) : K) ^ (m' * N)) := by
    rw [zpow_add₀ h3ne, mul_pow, div_mul_div_comm]
  have hxy' : ‖(x * y) ^ (N * N') / ((p : ℕ) : K) ^ (m * N' + m' * N) - 1‖ < 1 := by
    rw [hxy]
    exact norm_mul_sub_one_lt hx' hy'
  rw [iwasawaLog_eq_div h3 hNN hxy', iwasawaLog_eq_div h3 hNN hx', iwasawaLog_eq_div h3 hNN hy',
    hxy, padicLog_mul h3 hx' hy', add_div]

/-- The Iwasawa logarithm of a finite product is the sum of the Iwasawa logarithms. -/
theorem iwasawaLog_prod {ι : Type*} {s : Finset ι} {f : ι → K}
    (hf : ∀ i ∈ s, HasIwasawaLog p (f i)) :
    iwasawaLog p (∏ i ∈ s, f i) = ∑ i ∈ s, iwasawaLog p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iwasawaLog_one h3]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      iwasawaLog_mul h3 (hf a (Finset.mem_insert_self a s))
        (HasIwasawaLog.prod fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

theorem iwasawaLog_inv {x : K} (hx : HasIwasawaLog p x) : iwasawaLog p x⁻¹ = -iwasawaLog p x := by
  obtain ⟨N, hN, m, h⟩ := hx
  have hinv : ‖x⁻¹ ^ N / ((p : ℕ) : K) ^ (-m) - 1‖ < 1 := by
    rw [inv_pow, zpow_neg, inv_div_inv, ← inv_div (x ^ N), norm_inv_sub_one h]
    exact h
  rw [iwasawaLog_eq_div h3 hN hinv, iwasawaLog_eq_div h3 hN h, inv_pow, zpow_neg, inv_div_inv,
    ← inv_div (x ^ N), padicLog_inv h3 h, neg_div]

theorem iwasawaLog_pow {x : K} (hx : HasIwasawaLog p x) (n : ℕ) :
    iwasawaLog p (x ^ n) = n * iwasawaLog p x := by
  obtain ⟨N, hN, m, h⟩ := hx
  have e : (x ^ n) ^ N / ((p : ℕ) : K) ^ (m * n) = (x ^ N / ((p : ℕ) : K) ^ m) ^ n := by
    rw [div_pow, ← pow_mul, ← pow_mul, mul_comm n N, zpow_mul, zpow_natCast]
  have hpow : ‖(x ^ n) ^ N / ((p : ℕ) : K) ^ (m * n) - 1‖ < 1 := by
    rw [e]
    exact norm_pow_sub_one_lt h n
  rw [iwasawaLog_eq_div h3 hN hpow, iwasawaLog_eq_div h3 hN h, e, padicLog_pow h3 h n,
    mul_div_assoc]

theorem iwasawaLog_zpow {x : K} (hx : HasIwasawaLog p x) (n : ℤ) :
    iwasawaLog p (x ^ n) = n * iwasawaLog p x := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, iwasawaLog_pow h3 hx k, Int.cast_natCast]
  · rw [zpow_neg, zpow_natCast, iwasawaLog_inv h3 (hx.pow k), iwasawaLog_pow h3 hx k, Int.cast_neg,
      Int.cast_natCast, neg_mul]

/-- Roots of unity have Iwasawa logarithm `0`. -/
theorem iwasawaLog_of_pow_eq_one {ζ : K} {N : ℕ} (hN : 0 < N) (hζ : ζ ^ N = 1) :
    iwasawaLog p ζ = 0 := by
  have h : ‖ζ ^ N / ((p : ℕ) : K) ^ (0 : ℤ) - 1‖ < 1 := by simp [hζ]
  rw [iwasawaLog_eq_div h3 hN h]
  simp [hζ]

/-- Multiplying by a power of `p` does not change the Iwasawa logarithm: this is the
`w = p^r · ζ · z ↦ log_p z` recipe of [Wiki]. -/
theorem iwasawaLog_mul_zpow_natCast_p {x : K} (hx : HasIwasawaLog p x) (j : ℤ) :
    iwasawaLog p (x * ((p : ℕ) : K) ^ j) = iwasawaLog p x := by
  rw [iwasawaLog_mul h3 hx (HasIwasawaLog.natCast_p.zpow j),
    iwasawaLog_zpow h3 HasIwasawaLog.natCast_p, iwasawaLog_natCast_p h3, mul_zero, add_zero]

end Iwasawa

/-! ### Instantiation on `ℚ_p`-bar and `ℂ_p` -/

section PadicComplex

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p‖ = 1/p < 1` in the algebraic closure of `ℚ_p`. -/
theorem PadicAlgCl.norm_natCast_p_lt_one : ‖((p : ℕ) : PadicAlgCl p)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p‖ = 1/p < 1` in `ℂ_[p]`. -/
theorem PadicComplex.norm_natCast_p_lt_one : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends]
  exact PadicAlgCl.norm_natCast_p_lt_one

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Elements of `ℂ_[p]` integral over `ℤ` have norm at most `1`. -/
theorem PadicComplex.norm_le_one_of_isIntegral {x : ℂ_[p]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have hx' : IsIntegral (𝓞_ℂ_[p]) x := hx.tower_top
  have hv : Valued.v x ≤ 1 := (PadicComplexInt.integers p).isIntegral_iff_v_le_one.mp hx'
  rw [PadicComplex.norm_eq_norm]
  simp only [Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding]
  rw [Valuation.embedding_restrict]
  exact_mod_cast hv

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **Value group of `ℚ_p`-bar is `p^ℚ`**: for `y ≠ 0` algebraic over `ℚ_p`, `‖y‖ ^ n = ‖a₀‖` with
`n = deg (minpoly y)` and `a₀ = (minpoly y).coeff 0 ∈ ℚ_p^×`, so `‖y ^ n / p ^ a‖ = 1` for
`a = v_p(a₀)`. -/
theorem PadicAlgCl.exists_norm_pow_div_zpow_eq_one {y : PadicAlgCl p} (hy : y ≠ 0) :
    ∃ b : ℕ, 0 < b ∧ ∃ a : ℤ, ‖y ^ b / ((p : ℕ) : PadicAlgCl p) ^ a‖ = 1 := by
  have hint : IsIntegral ℚ_[p] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  set n := (minpoly ℚ_[p] y).natDegree with hn_def
  have hn : 0 < n := minpoly.natDegree_pos hint
  set a₀ := (minpoly ℚ_[p] y).coeff 0 with ha₀_def
  have ha₀ : a₀ ≠ 0 := minpoly.coeff_zero_ne_zero hint hy
  have h1 : ‖y‖ = ‖a₀‖ ^ (1 / n : ℝ) := by
    rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow]
  have h2 : ‖y‖ ^ n = ‖a₀‖ := by
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      one_div_mul_cancel (by exact_mod_cast hn.ne'), Real.rpow_one]
  have h3 : ‖a₀‖ = (p : ℝ) ^ (-a₀.valuation) := Padic.norm_eq_zpow_neg_valuation ha₀
  have h4 : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  refine ⟨n, hn, a₀.valuation, ?_⟩
  rw [norm_div, norm_pow, norm_zpow, h2, h3, h4, inv_zpow', div_self (zpow_ne_zero _ hp0.ne')]

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **Units of `ℚ_p`-bar have a `1`-unit power**: the powers of `u` lie in the unit ball of the
finite-dimensional `ℚ_p`-space `ℚ_p[u]`, which is compact, so `‖u ^ j - u ^ i‖ < 1` for some
`i < j`, and then `‖u ^ (j - i) - 1‖ < 1`. -/
theorem PadicAlgCl.hasPrincipalUnitPow_of_norm_eq_one {u : PadicAlgCl p} (hu : ‖u‖ = 1) :
    HasPrincipalUnitPow u := by
  have hint : IsIntegral ℚ_[p] u := (Algebra.IsAlgebraic.isAlgebraic u).isIntegral
  set S : Submodule ℚ_[p] (PadicAlgCl p) := Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] {u})
    with hS
  have : FiniteDimensional ℚ_[p] S := Module.Finite.iff_fg.2 hint.fg_adjoin_singleton
  have : ProperSpace S := FiniteDimensional.proper ℚ_[p] S
  have hmem : ∀ k : ℕ, u ^ k ∈ S := fun k =>
    Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] u) k
  set s : ℕ → S := fun k => ⟨u ^ k, hmem k⟩ with hs_def
  have hs : ∀ k, s k ∈ Metric.closedBall (0 : S) 1 := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right, Submodule.coe_norm]
    show ‖u ^ k‖ ≤ 1
    rw [norm_pow, hu, one_pow]
  obtain ⟨L, -, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : S) 1).tendsto_subseq hs
  obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.1 hlim (1 / 2) (by norm_num)
  have h1 : dist (s (ψ (k₀ + 1))) L < 1 / 2 := hk₀ _ (Nat.le_succ _)
  have h2 : dist (s (ψ k₀)) L < 1 / 2 := hk₀ _ le_rfl
  have hij : ψ k₀ < ψ (k₀ + 1) := hψ (Nat.lt_succ_self _)
  have hd : dist (s (ψ (k₀ + 1))) (s (ψ k₀)) < 1 := by
    calc dist (s (ψ (k₀ + 1))) (s (ψ k₀))
        ≤ dist (s (ψ (k₀ + 1))) L + dist (s (ψ k₀)) L := dist_triangle_right _ _ _
      _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
      _ = 1 := by norm_num
  refine ⟨ψ (k₀ + 1) - ψ k₀, Nat.sub_pos_of_lt hij, ?_⟩
  have hpow : u ^ ψ (k₀ + 1) = u ^ ψ k₀ * u ^ (ψ (k₀ + 1) - ψ k₀) := by
    rw [← pow_add, Nat.add_sub_cancel' hij.le]
  have hnorm : ‖u ^ ψ (k₀ + 1) - u ^ ψ k₀‖ = ‖u ^ (ψ (k₀ + 1) - ψ k₀) - 1‖ := by
    rw [hpow, ← mul_sub_one, norm_mul, norm_pow, hu, one_pow, one_mul]
  have hdist : dist (s (ψ (k₀ + 1))) (s (ψ k₀)) = ‖u ^ ψ (k₀ + 1) - u ^ ψ k₀‖ := by
    rw [dist_eq_norm, Submodule.coe_norm, Submodule.coe_sub]
  rw [← hnorm, ← hdist]
  exact hd

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Every nonzero element of `ℚ_p`-bar has an Iwasawa logarithm. -/
theorem PadicAlgCl.hasIwasawaLog {y : PadicAlgCl p} (hy : y ≠ 0) : HasIwasawaLog p y := by
  obtain ⟨b, hb, a, h1⟩ := PadicAlgCl.exists_norm_pow_div_zpow_eq_one hy
  obtain ⟨N, hN, h2⟩ := PadicAlgCl.hasPrincipalUnitPow_of_norm_eq_one h1
  refine ⟨b * N, Nat.mul_pos hb hN, a * N, ?_⟩
  rwa [pow_mul, zpow_mul, zpow_natCast, ← div_pow]

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Density of `ℚ_p`-bar in `ℂ_p`, in the form needed here: every `x ≠ 0` is within `‖x‖` of an
algebraic element (so `x / y` is a `1`-unit). -/
theorem PadicComplex.exists_norm_sub_coe_lt {x : ℂ_[p]} (hx : x ≠ 0) :
    ∃ y : PadicAlgCl p, ‖x - y‖ < ‖x‖ := by
  obtain ⟨_, ⟨y, rfl⟩, hd⟩ := Metric.mem_closure_iff.1
    (UniformSpace.Completion.denseRange_coe x) ‖x‖ (norm_pos_iff.2 hx)
  exact ⟨y, by rwa [dist_eq_norm] at hd⟩

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Every unit of `ℂ_p` has a `1`-unit power: `u = y · z` with `y` algebraic of norm `1` and
`‖z - 1‖ < 1`. -/
theorem PadicComplex.hasPrincipalUnitPow_of_norm_eq_one {u : ℂ_[p]} (hu : ‖u‖ = 1) :
    HasPrincipalUnitPow u := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  obtain ⟨y, hy⟩ := PadicComplex.exists_norm_sub_coe_lt hu0
  rw [hu] at hy
  have hyu : ‖(y : ℂ_[p]) - u‖ < 1 := by rwa [norm_sub_rev]
  have hyn : ‖(y : ℂ_[p])‖ = 1 := by
    have h : (y : ℂ_[p]) = u + ((y : ℂ_[p]) - u) := by ring
    rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hu]; exact hyu.ne'), hu,
      max_eq_left hyu.le]
  have hY : HasPrincipalUnitPow (y : ℂ_[p]) := by
    have h1 : ‖y‖ = 1 := by rwa [← PadicComplex.norm_extends]
    exact (PadicAlgCl.hasPrincipalUnitPow_of_norm_eq_one h1).map (algebraMap (PadicAlgCl p) ℂ_[p])
      (PadicComplex.norm_extends p)
  have hy0 : (y : ℂ_[p]) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hyn
    exact zero_ne_one hyn
  have hz : ‖u / y - 1‖ < 1 := by
    rw [div_sub_one hy0, norm_div, hyn, div_one]
    exact hy
  have e : (y : ℂ_[p]) * (u / y) = u := by rw [mul_comm, div_mul_cancel₀ _ hy0]
  rw [← e]
  exact hY.mul (HasPrincipalUnitPow.of_norm_sub_one_lt hz)

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **The Iwasawa logarithm is defined on all of `ℂ_p^×`** [Wiki]: `x = y · (x / y)` with `y`
algebraic and `x / y` a `1`-unit. -/
theorem PadicComplex.hasIwasawaLog {x : ℂ_[p]} (hx : x ≠ 0) : HasIwasawaLog p x := by
  obtain ⟨y, hy⟩ := PadicComplex.exists_norm_sub_coe_lt hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hyx : ‖(y : ℂ_[p])‖ = ‖x‖ := by
    have h : (y : ℂ_[p]) = x + ((y : ℂ_[p]) - x) := by ring
    rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_sub_rev]; exact hy.ne'),
      max_eq_left (by rw [norm_sub_rev]; exact hy.le)]
  have hy0 : (y : ℂ_[p]) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hyx
    exact hxpos.ne hyx
  have hY : HasIwasawaLog p (y : ℂ_[p]) := by
    have hy0' : y ≠ 0 := by
      rintro rfl
      simp at hy0
    exact (PadicAlgCl.hasIwasawaLog hy0').map (algebraMap (PadicAlgCl p) ℂ_[p])
      (PadicComplex.norm_extends p)
  have hz : ‖x / y - 1‖ < 1 := by
    rw [div_sub_one hy0, norm_div, hyx, div_lt_one hxpos]
    exact hy
  have e : (y : ℂ_[p]) * (x / y) = x := by rw [mul_comm, div_mul_cancel₀ _ hy0]
  rw [← e]
  exact hY.mul (HasIwasawaLog.of_norm_sub_one_lt hz)

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem PadicComplex.hasIwasawaLog_iff {x : ℂ_[p]} : HasIwasawaLog p x ↔ x ≠ 0 := by
  exact ⟨HasIwasawaLog.ne_zero, PadicComplex.hasIwasawaLog⟩

end PadicComplex

end PadicExpLog
