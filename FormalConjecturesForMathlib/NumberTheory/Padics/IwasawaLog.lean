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
public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The Iwasawa `p`-adic logarithm

The `p`-adic logarithm `log u = -∑ₙ (1 - u)^(n+1) / (n+1)`, converging on the open disc
`‖u - 1‖ < 1` of an abstract complete ultrametric field `K` of characteristic zero, and Iwasawa's
extension of it to those `x` some positive power of which is a `1`-unit times a power of `p` —
which in `K = ℂ_[p]` is every nonzero element.

## Main definitions

* `padicLog`: the logarithm series, converging on the whole open disc `‖u - 1‖ < 1`.
* `HasIwasawaLog p x`: some power `x ^ N` (`N ≥ 1`) is a `1`-unit times a power of `p`.
* `iwasawaLog p`: the Iwasawa logarithm, the extension of `padicLog` to `HasIwasawaLog p`
  characterised by being a homomorphism with `log p = 0`.

## Main results

* `PadicComplex.hasIwasawaLog_iff`: every nonzero element of `ℂ_[p]` has an Iwasawa logarithm.

## Scope

This file carries only what `FormalConjectures.Paper.GrossKuzmin` uses: `iwasawaLog` is the
`log_p` of Gross's regulator map, and `hasIwasawaLog_iff` is what shows that no junk value of
`iwasawaLog` is involved there. The analytic theory is deliberately omitted — that `padicLog`
converges and turns products into sums, that `iwasawaLog` is well defined independently of the
choice of `N` and `m` below and is a homomorphism with `log p = 0`, and the `p`-adic exponential
and its inverse relationship with the logarithm for odd `p`. Those are stated in the references
and would be the content of a full Mathlib development.

## References

* [Con] K. Conrad, *Infinite series in p-adic fields*, §8 (the logarithm).
* [Kob84] N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Ch. IV.
* [Wiki] Wikipedia, *p-adic exponential function* (the Iwasawa logarithm).
-/

@[expose] public section

namespace PadicIwasawaLog

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

section Log

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The ultrametric logarithm `log u = -∑ₙ (1 - u)^(n+1) / (n+1)`, converging for
`‖u - 1‖ < 1`; junk value otherwise.  [Kob84, Ch. IV §1]. -/
noncomputable def padicLog (u : K) : K :=
  -∑' n : ℕ, (1 - u) ^ (n + 1) / (n + 1)

omit [CompleteSpace K] [CharZero K] in
/-- A `1`-unit has norm one: `‖1 + x‖ = 1` as soon as `‖x‖ < 1`. -/
theorem norm_eq_one_of_norm_sub_one_lt_one {u : K} (hu : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have h : u = 1 + (u - 1) := by ring
  rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hu.ne'),
    norm_one, max_eq_left hu.le]

end Log

/-! ### The unit disc is closed under multiplication and powers -/

section OneUnits

omit [CompleteSpace K] [CharZero K] in
/-- The `1`-units are closed under multiplication:
`‖uv - 1‖ = ‖(u - 1)v + (v - 1)‖ ≤ max (‖u - 1‖ * ‖v‖) ‖v - 1‖ < 1`. [Con, p. 27]. -/
theorem norm_mul_sub_one_lt {u v : K} (hu : ‖u - 1‖ < 1) (hv : ‖v - 1‖ < 1) :
    ‖u * v - 1‖ < 1 := by
  have h : u * v - 1 = (u - 1) * v + (v - 1) := by ring
  rw [h]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hv)
  rw [norm_mul, norm_eq_one_of_norm_sub_one_lt_one hv, mul_one]
  exact hu

omit [CompleteSpace K] [CharZero K] in
/-- The `1`-units are closed under powers, by induction from `norm_mul_sub_one_lt`. -/
theorem norm_pow_sub_one_lt {u : K} (hu : ‖u - 1‖ < 1) (n : ℕ) : ‖u ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact norm_mul_sub_one_lt ih hu

end OneUnits

/-! ### The Iwasawa logarithm: its domain, and its definition -/

section Iwasawa

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `HasPrincipalUnitPow u` says that some positive power of `u` is a `1`-unit, `‖u ^ m - 1‖ < 1`.
This holds for every unit of the valuation ring of a field whose residue field is algebraic
over `𝔽_p` — finite extensions of `ℚ_p`, `ℚ_p`-bar and `ℂ_p` — of which only the `ℚ_p`-bar case
is proved here (`PadicAlgCl.hasPrincipalUnitPow_of_norm_eq_one`). -/
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
[Wiki]. Concretely `iwasawaLog p x = padicLog (x ^ N / p ^ m) / N` for `N ≥ 1`, `m` with
`‖x ^ N / p ^ m - 1‖ < 1`; the value is independent of that choice, though this file does not
prove it, and to fix a value here `N` is taken least and `m` by choice. Junk value `0` outside
the domain. -/
noncomputable def iwasawaLog (x : K) : K := by
  classical
  exact if h : ∃ N : ℕ, 0 < N ∧ ∃ m : ℤ, ‖x ^ N / ((p : ℕ) : K) ^ m - 1‖ < 1 then
    padicLog (x ^ Nat.find h / ((p : ℕ) : K) ^ Classical.choose (Nat.find_spec h).2) /
      (Nat.find h : K)
  else 0

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A `1`-unit lies in the domain of the Iwasawa logarithm: take `N = 1` and `m = 0`. -/
theorem HasIwasawaLog.of_norm_sub_one_lt {u : K} (hu : ‖u - 1‖ < 1) : HasIwasawaLog p u :=
  ⟨1, one_pos, 0, by simpa using hu⟩

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Only nonzero elements have an Iwasawa logarithm, since `0 ^ N / p ^ m - 1 = -1`. -/
theorem HasIwasawaLog.ne_zero {x : K} (hx : HasIwasawaLog p x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨N, hN, m, h⟩ := hx
  rw [zero_pow hN.ne', zero_div, zero_sub, norm_neg, norm_one] at h
  exact lt_irrefl _ h

omit [CompleteSpace K] in
/-- The domain of the Iwasawa logarithm is closed under multiplication: if `x ^ N / p ^ m` and
`y ^ N' / p ^ m'` are `1`-units, then so is `(x * y) ^ (N * N') / p ^ (m * N' + m' * N)`, which
is their product of powers. -/
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

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `HasIwasawaLog` is transported along norm-preserving ring homomorphisms
(e.g. `ℚ_p`-bar → `ℂ_p`). -/
theorem HasIwasawaLog.map {L : Type*} [NontriviallyNormedField L] (f : K →+* L)
    (hf : ∀ y : K, ‖f y‖ = ‖y‖) {x : K} (hx : HasIwasawaLog p x) : HasIwasawaLog p (f x) := by
  obtain ⟨N, hN, m, h⟩ := hx
  refine ⟨N, hN, m, ?_⟩
  rw [← map_natCast f, ← map_zpow₀, ← map_pow, ← map_div₀, ← map_one f, ← map_sub, hf]
  exact h

end Iwasawa

/-! ### Instantiation on `ℚ_p`-bar and `ℂ_p` -/

section PadicComplex

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p‖ = 1/p` in `ℚ_p`-bar, since the norm there extends the one of `ℚ_p`. -/
theorem PadicAlgCl.norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p‖ = 1/p < 1` in `ℂ_[p]`. -/
theorem PadicComplex.norm_natCast_p_lt_one : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends, PadicAlgCl.norm_natCast_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

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
  have h4 : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := PadicAlgCl.norm_natCast_p
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
/-- The domain of the Iwasawa logarithm in `ℂ_[p]` is exactly `ℂ_[p]^×`. -/
theorem PadicComplex.hasIwasawaLog_iff {x : ℂ_[p]} : HasIwasawaLog p x ↔ x ≠ 0 :=
  ⟨HasIwasawaLog.ne_zero, PadicComplex.hasIwasawaLog⟩

end PadicComplex

end PadicIwasawaLog
