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
public import FormalConjecturesForMathlib.Leopoldt.NumberTheory.Padics.ExpLog

/-!
# `p`-adic powers of principal units

Let `K` be a complete ultrametric field of characteristic zero with `‖p‖ < 1`, for instance a
finite extension of `ℚ_p`, the field `ℂ_[p]`, or the completion of a number field at a prime
above `p`. The principal units, or `1`-units, `oneUnits K = {u : Kˣ | ‖u - 1‖ < 1}` form a
pro-`p` group: `u ^ (p ^ k) → 1`. Hence a principal unit `x` has `p`-adic powers
`x ^ a = lim x ^ aₙ` for `a ∈ ℤ_p` and integers `aₙ → a`, and `Additive (oneUnits K)` is a
`ℤ_[p]`-module. Mathlib has no such module structure.

## Main definitions

* `oneUnits K`: the subgroup of `Kˣ` of principal units.
* `OneUnits.zpPow x a`: the `p`-adic power `x ^ a = lim x ^ (a.appr n)` of `x : K` by `a : ℤ_[p]`
  (junk value when the sequence does not converge, e.g. if `‖x - 1‖ ≥ 1`).
* `OneUnits.instModule`: the `ℤ_[p]`-module structure `a • u = u ^ a` on `Additive (oneUnits K)`.

## Main results

* `OneUnits.tendsto_zpow_of_tendsto`: `x ^ cₙ → x ^ a` for any integers `cₙ → a` in `ℤ_p`.
* `OneUnits.zpPow_add`, `OneUnits.zpPow_mul`, `OneUnits.mul_zpPow`: the exponent rules.
* `OneUnits.norm_zpPow_sub_zpPow_le`, `OneUnits.continuous_zpPow`: `x ^ a` is `1`-Lipschitz in
  `x` and continuous in `a`.
* `OneUnits.natCast_smul`, `OneUnits.intCast_smul`: integer `p`-adic powers are ordinary powers.
* `OneUnits.tendsto_appr_nsmul`: `a • u = lim (a.appr n) • u` on the module side.
* `AddSubgroup.smul_mem_of_isClosed`: closed subgroups are `ℤ_[p]`-submodules.

## References

* [Klo] B. Klopsch, *Five lectures on analytic pro-p groups*, LMS-EPSRC short course notes,
  Oxford 2007, Exercise 6.1 (d)–(f), p. 24: `g ^ λ := lim g ^ λₙ` and the exponent rules.
* [BG] O. Ben-Bassat, N. Gropper, *Arithmetic field theory via pro-p duality groups*,
  arXiv:2504.19078, §Notation and conventions, p. 4: the limit is independent of the sequence.
* [Con] K. Conrad, *Infinite series in p-adic fields*, pp. 13–14 (the strong triangle
  inequality for `x ^ n - y ^ n`) and p. 27 (the disc `|x - 1| < 1` is a group).
-/

@[expose] public section

open Filter Topology

/-- The integer approximations `a.appr n` of `a : ℤ_[p]` tend to `a`, since
`‖a - a.appr n‖ ≤ p ^ (-n)` (`PadicInt.appr_spec`). -/
theorem PadicInt.tendsto_appr {p : ℕ} [hp : Fact p.Prime] (a : ℤ_[p]) :
    Tendsto (fun n ↦ (a.appr n : ℤ_[p])) atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n : ℕ, ‖((a.appr n : ℤ_[p]) - a)‖ ≤ ((p : ℝ)⁻¹) ^ n := fun n ↦ by
    rw [norm_sub_rev]
    calc ‖a - (a.appr n : ℤ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) :=
          (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n a)
      _ = ((p : ℝ)⁻¹) ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
  have hp1 : ((p : ℝ)⁻¹) < 1 := by
    rw [inv_lt_one₀ (by exact_mod_cast hp.out.pos)]
    exact_mod_cast hp.out.one_lt
  exact squeeze_zero (fun n ↦ norm_nonneg _) hb
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hp1)

/-- The principal units, or `1`-units, of an ultrametric normed field: the units `u` with
`‖u - 1‖ < 1`. [Con, p. 27]. -/
def oneUnits (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] : Subgroup Kˣ where
  carrier := {u | ‖(u : K) - 1‖ < 1}
  mul_mem' hu hv := PadicExpLog.norm_mul_sub_one_lt hu hv
  one_mem' := by simp
  inv_mem' {u} hu := by
    show ‖((u⁻¹ : Kˣ) : K) - 1‖ < 1
    rw [Units.val_inv_eq_inv_val, PadicExpLog.norm_inv_sub_one hu]
    exact hu

namespace OneUnits

section Norm

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

@[simp]
theorem mem_oneUnits_iff {u : Kˣ} : u ∈ oneUnits K ↔ ‖(u : K) - 1‖ < 1 := Iff.rfl

/-- `x ^ n - y ^ n = (x - y) (x ^ (n - 1) + ⋯ + y ^ (n - 1))` and the strong triangle inequality.
[Con, pp. 13–14]. -/
theorem norm_pow_sub_pow_le {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  rw [← (Commute.all x y).geom_sum₂_mul n, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ ?_
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hx) (by positivity)
    (pow_le_one₀ (norm_nonneg _) hy)

/-- `norm_pow_sub_pow_le` at `y = 1`. -/
theorem norm_pow_sub_one_le {x : K} (hx : ‖x‖ ≤ 1) (n : ℕ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  simpa using norm_pow_sub_pow_le hx (norm_one (α := K)).le n

/-- Integer powers of a `1`-unit stay in the closed ball of radius `‖x - 1‖` around `1`. The
negative exponents use `‖x⁻¹ - 1‖ = ‖x - 1‖` [Con, p. 27]. -/
theorem norm_zpow_sub_one_le {x : K} (hx : ‖x - 1‖ < 1) (n : ℤ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  have hx1 : ‖x‖ ≤ 1 := (PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hx).le
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact norm_pow_sub_one_le hx1 m
  · rw [zpow_neg, zpow_natCast,
      PadicExpLog.norm_inv_sub_one (PadicExpLog.norm_pow_sub_one_lt hx m)]
    exact norm_pow_sub_one_le hx1 m

/-- Dividing by a `1`-unit is an isometry at `1`: `x / y - 1 = (x - y) / y` and `‖y‖ = 1`. -/
theorem norm_div_sub_one {x y : K} (hy : ‖y - 1‖ < 1) : ‖x / y - 1‖ = ‖x - y‖ := by
  have hy1 : ‖y‖ = 1 := PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hy
  have hy0 : y ≠ 0 := norm_pos_iff.1 (hy1 ▸ one_pos)
  have h : x / y - 1 = (x - y) / y := by field_simp
  rw [h, norm_div, hy1, div_one]

/-- Two `1`-units are at distance `< 1`, by the strong triangle inequality. -/
theorem norm_sub_lt_one {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) : ‖x - y‖ < 1 :=
  calc ‖x - y‖ = ‖(x - 1) + -(y - 1)‖ := by ring_nf
    _ ≤ max ‖x - 1‖ ‖-(y - 1)‖ := IsUltrametricDist.norm_add_le_max _ _
    _ = max ‖x - 1‖ ‖y - 1‖ := by rw [norm_neg]
    _ < 1 := max_lt hx hy

/-- `x ↦ x ^ n` is `1`-Lipschitz on the `1`-units: reduce to `norm_zpow_sub_one_le` for `x / y`
via `x ^ n - y ^ n = y ^ n ((x / y) ^ n - 1)`. -/
theorem norm_zpow_sub_zpow_le {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) (n : ℤ) :
    ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  have hy1 : ‖y‖ = 1 := PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hy
  have hy0 : y ≠ 0 := norm_pos_iff.1 (hy1 ▸ one_pos)
  have hdiv : ‖x / y - 1‖ < 1 := by
    rw [norm_div_sub_one hy]
    exact norm_sub_lt_one hx hy
  have he : x ^ n - y ^ n = y ^ n * ((x / y) ^ n - 1) := by
    rw [div_zpow, mul_sub, mul_one, mul_div_cancel₀ _ (zpow_ne_zero _ hy0)]
  rw [he, norm_mul, norm_zpow, hy1, one_zpow, one_mul, ← norm_div_sub_one (x := x) hy]
  exact norm_zpow_sub_one_le hdiv n

end Norm

section ZpPow

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [CharZero K] [Fact (‖((p : ℕ) : K)‖ < 1)]

/-- The uniform estimate behind everything: `‖x ^ m - 1‖` is small once `p ^ k ∣ m`, since
`x ^ (p ^ k) → 1` (`PadicExpLog.tendsto_pow_pow_sub_one`) and `‖y ^ j - 1‖ ≤ ‖y - 1‖`.
[Klo, Exercise 6.1 (d)]. -/
theorem exists_forall_norm_zpow_sub_one_lt {x : K} (hx : ‖x - 1‖ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ m : ℤ, (p : ℤ) ^ k ∣ m → ‖x ^ m - 1‖ < ε := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := Fact.out
  obtain ⟨k, hk⟩ := Metric.tendsto_atTop.1 (PadicExpLog.tendsto_pow_pow_sub_one h3 hx) ε hε
  refine ⟨k, fun m ⟨j, hj⟩ ↦ ?_⟩
  have hkk := hk k le_rfl
  rw [dist_zero_right] at hkk
  calc ‖x ^ m - 1‖ = ‖(x ^ ((p : ℤ) ^ k)) ^ j - 1‖ := by rw [← zpow_mul, ← hj]
    _ ≤ ‖x ^ ((p : ℤ) ^ k) - 1‖ := by
        refine norm_zpow_sub_one_le ?_ j
        rw [← Int.natCast_pow, zpow_natCast]
        exact PadicExpLog.norm_pow_sub_one_lt hx _
    _ < ε := by rwa [← Int.natCast_pow, zpow_natCast]

theorem tendsto_zpow_of_tendsto_zero {x : K} (hx : ‖x - 1‖ < 1) {c : ℕ → ℤ}
    (hc : Tendsto (fun n ↦ (c n : ℤ_[p])) atTop (𝓝 0)) :
    Tendsto (fun n ↦ x ^ c n) atTop (𝓝 1) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_forall_norm_zpow_sub_one_lt (p := p) hx hε
  have hp0 : (0:ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hc _ (by positivity : (0:ℝ) < (p : ℝ) ^ (-k : ℤ))
  refine ⟨N, fun n hn ↦ ?_⟩
  have h1 := hN n hn
  rw [dist_zero_right] at h1
  rw [dist_eq_norm]
  exact hk _ (by exact_mod_cast (PadicInt.norm_int_le_pow_iff_dvd (p := p)).1 h1.le)

/-- The `p`-adic expansions of `a` agree to higher and higher precision, so the integer powers
`x ^ (a.appr n)` form a Cauchy sequence [Klo, Exercise 6.1 (d)]: "show that the limit
`lim g ^ λₙ` exists". -/
theorem cauchySeq_pow_appr {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) :
    CauchySeq fun n ↦ x ^ a.appr n := by
  have hx0 : x ≠ 0 :=
    norm_pos_iff.1 ((PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hx) ▸ one_pos)
  refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_forall_norm_zpow_sub_one_lt (p := p) hx hε
  refine ⟨k, fun m hm n hn ↦ ?_⟩
  -- It suffices to treat `i ≤ j`, since `dist` is symmetric.
  have key : ∀ i j : ℕ, k ≤ i → i ≤ j → dist (x ^ a.appr j) (x ^ a.appr i) < ε := by
    intro i j hki hij
    have hdvd : ((p : ℤ) ^ k) ∣ ((a.appr j : ℤ) - (a.appr i : ℤ)) := by
      refine dvd_trans (pow_dvd_pow _ hki) ?_
      rw [← Nat.cast_sub (PadicInt.appr_mono a hij)]
      exact_mod_cast Int.natCast_dvd_natCast.2 (PadicInt.dvd_appr_sub_appr a i j hij)
    have he : x ^ a.appr j - x ^ a.appr i
        = x ^ (a.appr i : ℤ) * (x ^ ((a.appr j : ℤ) - (a.appr i : ℤ)) - 1) := by
      rw [mul_sub, mul_one, ← zpow_add₀ hx0]
      norm_num [zpow_natCast]
    rw [dist_eq_norm, he, norm_mul, norm_zpow,
      PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hx, one_zpow, one_mul]
    exact hk _ hdvd
  rcases le_total m n with h | h
  · rw [dist_comm]; exact key m n hm h
  · exact key n m hn h

/-- The `p`-adic power `x ^ a = lim x ^ (a.appr n)` of `x : K` by `a : ℤ_[p]`. This is the limit
of [Klo, Exercise 6.1 (d)] and [BG, p. 4], with `a.appr n` as the approximating integers. The
value is junk unless the sequence converges, which it does when `‖x - 1‖ < 1`
(`tendsto_pow_appr`). -/
noncomputable def zpPow (x : K) (a : ℤ_[p]) : K :=
  limUnder atTop fun n ↦ x ^ a.appr n

theorem tendsto_pow_appr {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) :
    Tendsto (fun n ↦ x ^ a.appr n) atTop (𝓝 (zpPow x a)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_pow_appr hx a))

/-- The limit does not depend on the approximating sequence [BG, p. 4]: "`x ^ λ = lim x ^ nᵢ`
for some sequence of integers `nᵢ` converging to `λ` (this is independent of the choice of
sequence)". Indeed `x ^ cₙ = x ^ (a.appr n) * x ^ (cₙ - a.appr n)` and the second factor tends
to `1` by `tendsto_zpow_of_tendsto_zero`. -/
theorem tendsto_zpow_of_tendsto {x : K} (hx : ‖x - 1‖ < 1) {c : ℕ → ℤ} {a : ℤ_[p]}
    (hc : Tendsto (fun n ↦ (c n : ℤ_[p])) atTop (𝓝 a)) :
    Tendsto (fun n ↦ x ^ c n) atTop (𝓝 (zpPow x a)) := by
  have hx0 : x ≠ 0 :=
    norm_pos_iff.1 ((PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hx) ▸ one_pos)
  have h0 : Tendsto (fun n ↦ ((c n - (a.appr n : ℤ) : ℤ) : ℤ_[p])) atTop (𝓝 0) := by
    have h := hc.sub (PadicInt.tendsto_appr a)
    rw [sub_self] at h
    refine h.congr fun n ↦ ?_
    push_cast
    ring
  have h1 := (tendsto_pow_appr hx a).mul (tendsto_zpow_of_tendsto_zero hx h0)
  rw [mul_one] at h1
  refine h1.congr fun n ↦ ?_
  rw [← zpow_natCast x (a.appr n), ← zpow_add₀ hx0]
  congr 1
  ring

theorem zpPow_intCast {x : K} (hx : ‖x - 1‖ < 1) (n : ℤ) : zpPow x (n : ℤ_[p]) = x ^ n :=
  tendsto_nhds_unique (tendsto_zpow_of_tendsto (p := p) hx (c := fun _ ↦ n) tendsto_const_nhds)
    tendsto_const_nhds

theorem zpPow_natCast {x : K} (hx : ‖x - 1‖ < 1) (n : ℕ) : zpPow x (n : ℤ_[p]) = x ^ n := by
  have h : ((n : ℤ) : ℤ_[p]) = (n : ℤ_[p]) := by push_cast; ring
  rw [← h, zpPow_intCast hx (n : ℤ), zpow_natCast]

@[simp]
theorem zpPow_zero {x : K} (hx : ‖x - 1‖ < 1) : zpPow x (0 : ℤ_[p]) = 1 := by
  simpa using zpPow_intCast hx 0

@[simp]
theorem zpPow_one {x : K} (hx : ‖x - 1‖ < 1) : zpPow x (1 : ℤ_[p]) = x := by
  simpa using zpPow_intCast hx 1

@[simp]
theorem one_zpPow (a : ℤ_[p]) : zpPow (1 : K) a = 1 := by
  refine tendsto_nhds_unique (tendsto_pow_appr (p := p) (by simp) a) ?_
  simp

/-- `g ^ (λ + μ) = g ^ λ * g ^ μ` [Klo, Exercise 6.1 (d)]. Compute the limit along
`a.appr n + b.appr n`, which also tends to `a + b`. -/
theorem zpPow_add {x : K} (hx : ‖x - 1‖ < 1) (a b : ℤ_[p]) :
    zpPow x (a + b) = zpPow x a * zpPow x b := by
  have hx0 : x ≠ 0 :=
    norm_pos_iff.1 ((PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hx) ▸ one_pos)
  have hc : Tendsto (fun n ↦ (((a.appr n : ℤ) + (b.appr n : ℤ) : ℤ) : ℤ_[p])) atTop
      (𝓝 (a + b)) := by
    refine ((PadicInt.tendsto_appr a).add (PadicInt.tendsto_appr b)).congr fun n ↦ ?_
    push_cast
    ring
  refine tendsto_nhds_unique ((tendsto_zpow_of_tendsto hx hc).congr fun n ↦ ?_)
    ((tendsto_pow_appr hx a).mul (tendsto_pow_appr hx b))
  rw [zpow_add₀ hx0, zpow_natCast, zpow_natCast]

theorem zpPow_neg {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) : zpPow x (-a) = (zpPow x a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← zpPow_add hx, neg_add_cancel, zpPow_zero hx]

/-- `(g h) ^ λ = g ^ λ * h ^ λ` for commuting `g, h` [Klo, Exercise 6.1 (d)]: the "sufficient
condition" of the exercise is automatic in a field. -/
theorem mul_zpPow {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) (a : ℤ_[p]) :
    zpPow (x * y) a = zpPow x a * zpPow y a := by
  refine tendsto_nhds_unique (tendsto_pow_appr (PadicExpLog.norm_mul_sub_one_lt hx hy) a) ?_
  simpa only [mul_pow] using (tendsto_pow_appr hx a).mul (tendsto_pow_appr hy a)

/-- `p`-adic powers stay in the closed ball of radius `‖x - 1‖` around `1`: the bound
`norm_pow_sub_one_le` passes to the limit. This is the image of `ℤ_[p] → cl⟨x⟩` of
[Klo, Exercise 6.1 (e)]. -/
theorem norm_zpPow_sub_one_le {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) :
    ‖zpPow x a - 1‖ ≤ ‖x - 1‖ :=
  le_of_tendsto (((tendsto_pow_appr hx a).sub_const 1).norm) <| Eventually.of_forall fun _ ↦
    norm_pow_sub_one_le (PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hx).le _

theorem norm_zpPow_sub_one_lt {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) :
    ‖zpPow x a - 1‖ < 1 :=
  (norm_zpPow_sub_one_le hx a).trans_lt hx

@[simp]
theorem norm_zpPow {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) : ‖zpPow x a‖ = 1 :=
  PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one (norm_zpPow_sub_one_lt hx a)

theorem zpPow_ne_zero {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) : zpPow x a ≠ 0 :=
  norm_pos_iff.1 ((norm_zpPow hx a) ▸ one_pos)

/-- `x ↦ x ^ a` is `1`-Lipschitz on the principal units: `norm_pow_sub_pow_le` in the limit. -/
theorem norm_zpPow_sub_zpPow_le {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) (a : ℤ_[p]) :
    ‖zpPow x a - zpPow y a‖ ≤ ‖x - y‖ :=
  le_of_tendsto (((tendsto_pow_appr hx a).sub (tendsto_pow_appr hy a)).norm) <|
    Eventually.of_forall fun _ ↦
      norm_pow_sub_pow_le (PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hx).le
        (PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hy).le _

/-- `g ^ (λ μ) = (g ^ μ) ^ λ` [Klo, Exercise 6.1 (d)]. A double limit: the sequence
`(x ^ b.appr n) ^ a.appr n` tends to `x ^ (a * b)` because the exponents multiply, and to
`(x ^ b) ^ a` because `x ^ b.appr n → x ^ b` and `y ↦ y ^ m` is `1`-Lipschitz on the unit ball
(`norm_pow_sub_pow_le`), uniformly in `m`. -/
theorem zpPow_mul {x : K} (hx : ‖x - 1‖ < 1) (a b : ℤ_[p]) :
    zpPow x (a * b) = zpPow (zpPow x b) a := by
  have hxb : ‖zpPow x b - 1‖ < 1 := norm_zpPow_sub_one_lt hx b
  have hx1 : ‖x‖ ≤ 1 := (PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one hx).le
  have hb1 : ‖zpPow x b‖ ≤ 1 := (norm_zpPow hx b).le
  have hc : Tendsto (fun n ↦ (((a.appr n : ℤ) * (b.appr n : ℤ) : ℤ) : ℤ_[p])) atTop
      (𝓝 (a * b)) := by
    refine ((PadicInt.tendsto_appr a).mul (PadicInt.tendsto_appr b)).congr fun n ↦ ?_
    push_cast
    ring
  have h1 : Tendsto (fun n ↦ (x ^ b.appr n) ^ a.appr n) atTop (𝓝 (zpPow x (a * b))) := by
    refine (tendsto_zpow_of_tendsto hx hc).congr fun n ↦ ?_
    rw [← pow_mul, ← zpow_natCast x (b.appr n * a.appr n)]
    push_cast
    rw [mul_comm]
  have h2 : Tendsto (fun n ↦ (x ^ b.appr n) ^ a.appr n) atTop (𝓝 (zpPow (zpPow x b) a)) := by
    refine (tendsto_pow_appr hxb a).congr_dist ?_
    have hbound : ∀ n : ℕ, dist ((zpPow x b) ^ a.appr n) ((x ^ b.appr n) ^ a.appr n)
        ≤ ‖zpPow x b - x ^ b.appr n‖ := fun n ↦ by
      rw [dist_eq_norm]
      exact norm_pow_sub_pow_le hb1
        (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx1) _
    refine squeeze_zero (fun _ ↦ dist_nonneg) hbound ?_
    have h := tendsto_pow_appr hx b
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    simpa only [norm_sub_rev] using h
  exact tendsto_nhds_unique h1 h2

/-- When `p ^ k ∣ a`, the power `x ^ a` is as close to `1` as `x ^ (p ^ k)` is: write
`a = p ^ k * d` and use `zpPow_mul`. -/
theorem norm_zpPow_sub_one_le_of_dvd {x : K} (hx : ‖x - 1‖ < 1) {a : ℤ_[p]} {k : ℕ}
    (h : (p : ℤ_[p]) ^ k ∣ a) : ‖zpPow x a - 1‖ ≤ ‖x ^ p ^ k - 1‖ := by
  obtain ⟨d, rfl⟩ := h
  have hcast : ((p : ℤ_[p]) ^ k) = ((p ^ k : ℕ) : ℤ_[p]) := by push_cast; ring
  rw [mul_comm, zpPow_mul hx, hcast, zpPow_natCast hx]
  exact norm_zpPow_sub_one_le (PadicExpLog.norm_pow_sub_one_lt hx _) d

/-- `a ↦ x ^ a` is continuous on `ℤ_[p]`: if `‖a - b‖ ≤ p ^ (-k)` then `p ^ k ∣ a - b`, and
`x ^ a - x ^ b = x ^ b (x ^ (a - b) - 1)` is small by `norm_zpPow_sub_one_le_of_dvd`. -/
theorem continuous_zpPow {x : K} (hx : ‖x - 1‖ < 1) : Continuous fun a : ℤ_[p] ↦ zpPow x a := by
  refine Metric.continuous_iff.2 fun b ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_forall_norm_zpow_sub_one_lt (p := p) hx hε
  have hp0 : (0:ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨(p : ℝ) ^ (-k : ℤ), by positivity, fun a ha ↦ ?_⟩
  rw [dist_eq_norm] at ha ⊢
  have hdvd : (p : ℤ_[p]) ^ k ∣ (a - b) :=
    Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow (a - b) k).1 ha.le)
  have he : zpPow x a - zpPow x b = zpPow x b * (zpPow x (a - b) - 1) := by
    rw [mul_sub, mul_one, ← zpPow_add hx, add_sub_cancel]
  rw [he, norm_mul, norm_zpPow hx, one_mul]
  refine lt_of_le_of_lt (norm_zpPow_sub_one_le_of_dvd hx hdvd) ?_
  have h := hk ((p : ℤ) ^ k) dvd_rfl
  rwa [← Int.natCast_pow, zpow_natCast] at h

end ZpPow

section Module

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [CharZero K] [Fact (‖((p : ℕ) : K)‖ < 1)]

/-- The `p`-adic power of a principal unit, as a principal unit. -/
noncomputable def zpPowUnit (u : oneUnits K) (a : ℤ_[p]) : oneUnits K :=
  ⟨Units.mk0 (zpPow ((u : Kˣ) : K) a) (zpPow_ne_zero (mem_oneUnits_iff.1 u.2) a),
    mem_oneUnits_iff.2 (norm_zpPow_sub_one_lt (mem_oneUnits_iff.1 u.2) a)⟩

noncomputable instance instSMul : SMul ℤ_[p] (Additive (oneUnits K)) :=
  ⟨fun a u ↦ Additive.ofMul (zpPowUnit u.toMul a)⟩

theorem toMul_smul (a : ℤ_[p]) (u : Additive (oneUnits K)) :
    (a • u).toMul = zpPowUnit u.toMul a := rfl

@[simp]
theorem coe_smul (a : ℤ_[p]) (u : Additive (oneUnits K)) :
    (((a • u).toMul : Kˣ) : K) = zpPow ((u.toMul : Kˣ) : K) a := rfl

omit [CompleteSpace K] [CharZero K] in
/-- Two elements of `Additive (oneUnits K)` are equal as soon as their values in `K` are. -/
theorem ext_of_coe {u v : Additive (oneUnits K)}
    (h : ((u.toMul : Kˣ) : K) = ((v.toMul : Kˣ) : K)) : u = v :=
  Additive.toMul.injective (Subtype.ext (Units.ext h))

/-- The `ℤ_[p]`-module structure `a • u = u ^ a` on the principal units. "Regard `G` as a
finitely generated `ℤ_p`-module" [Klo, Exercise 6.1 (f)]; the six axioms are the exponent rules
`zpPow_one`, `zpPow_mul`, `one_zpPow`, `mul_zpPow`, `zpPow_add`, `zpPow_zero` of
[Klo, Exercise 6.1 (d)], read additively. -/
noncomputable instance instModule : Module ℤ_[p] (Additive (oneUnits K)) where
  one_smul u := ext_of_coe <| by
    rw [coe_smul]; exact zpPow_one (mem_oneUnits_iff.1 u.toMul.2)
  mul_smul a b u := ext_of_coe <| by
    rw [coe_smul, coe_smul, coe_smul]; exact zpPow_mul (mem_oneUnits_iff.1 u.toMul.2) a b
  smul_zero a := ext_of_coe <| by
    rw [coe_smul]; exact one_zpPow a
  smul_add a u v := ext_of_coe <| by
    rw [coe_smul]
    have hval : (((u + v).toMul : oneUnits K) : Kˣ) = ((u.toMul : Kˣ) * (v.toMul : Kˣ)) := rfl
    rw [hval, Units.val_mul,
      mul_zpPow (mem_oneUnits_iff.1 u.toMul.2) (mem_oneUnits_iff.1 v.toMul.2) a]
    rfl
  add_smul a b u := ext_of_coe <| by
    rw [coe_smul, zpPow_add (mem_oneUnits_iff.1 u.toMul.2) a b]; rfl
  zero_smul u := ext_of_coe <| by
    rw [coe_smul]; exact zpPow_zero (mem_oneUnits_iff.1 u.toMul.2)

theorem natCast_smul (n : ℕ) (u : Additive (oneUnits K)) : (n : ℤ_[p]) • u = n • u := by
  refine ext_of_coe ?_
  rw [coe_smul, zpPow_natCast (mem_oneUnits_iff.1 u.toMul.2), toMul_nsmul]
  push_cast
  ring

theorem intCast_smul (n : ℤ) (u : Additive (oneUnits K)) : (n : ℤ_[p]) • u = n • u := by
  refine ext_of_coe ?_
  rw [coe_smul, zpPow_intCast (mem_oneUnits_iff.1 u.toMul.2), toMul_zsmul]
  push_cast
  ring

instance : T2Space (Additive (oneUnits K)) := inferInstanceAs (T2Space (oneUnits K))

omit [CompleteSpace K] [CharZero K] [Fact (‖((p : ℕ) : K)‖ < 1)] in
/-- The topology of `Additive (oneUnits K)` is induced from `K`: the subgroup carries the
subtype topology of `Kˣ`, which embeds in `K` (`Units.isEmbedding_val₀`), and `Additive` shares
the topology of the underlying type. -/
theorem isInducing_coe :
    Topology.IsInducing (fun u : Additive (oneUnits K) ↦ ((u.toMul : Kˣ) : K)) :=
  Units.isEmbedding_val₀.isInducing.comp Topology.IsInducing.subtypeVal

/-- `a • u = lim (a.appr n) • u`, the defining limit on the module side. -/
theorem tendsto_appr_nsmul (a : ℤ_[p]) (u : Additive (oneUnits K)) :
    Tendsto (fun n ↦ a.appr n • u) atTop (𝓝 (a • u)) := by
  rw [isInducing_coe.tendsto_nhds_iff]
  have hu : ‖((u.toMul : Kˣ) : K) - 1‖ < 1 := mem_oneUnits_iff.1 u.toMul.2
  refine (tendsto_pow_appr (p := p) hu a).congr fun n ↦ ?_
  rw [Function.comp_apply, ← natCast_smul (p := p) (a.appr n) u, coe_smul, zpPow_natCast hu]

theorem continuous_smul_const (u : Additive (oneUnits K)) :
    Continuous fun a : ℤ_[p] ↦ a • u := by
  rw [isInducing_coe.continuous_iff]
  refine (continuous_zpPow (p := p) (mem_oneUnits_iff.1 u.toMul.2)).congr fun a ↦ ?_
  rw [Function.comp_apply, coe_smul]

/-- `x ↦ x ^ a` is continuous on the open unit ball around `1`, being `1`-Lipschitz there
(`norm_zpPow_sub_zpPow_le`). -/
theorem continuousOn_zpPow (a : ℤ_[p]) :
    ContinuousOn (fun x : K ↦ zpPow x a) {x : K | ‖x - 1‖ < 1} := by
  refine Metric.continuousOn_iff.2 fun x hx ε hε ↦ ⟨ε, hε, fun y hy hdist ↦ ?_⟩
  rw [dist_eq_norm] at hdist ⊢
  exact lt_of_le_of_lt (norm_zpPow_sub_zpPow_le hy hx a) hdist

instance : ContinuousConstSMul ℤ_[p] (Additive (oneUnits K)) where
  continuous_const_smul a := by
    rw [isInducing_coe.continuous_iff]
    refine ((continuousOn_zpPow (K := K) a).comp_continuous isInducing_coe.continuous
      fun u ↦ mem_oneUnits_iff.1 u.toMul.2).congr fun u ↦ ?_
    rw [Function.comp_apply, Function.comp_apply, coe_smul]

/-- A closed subgroup of a `ℤ_[p]`-module in which `a • x = lim (a.appr n) • x` is a
`ℤ_[p]`-submodule. -/
theorem _root_.AddSubgroup.smul_mem_of_isClosed {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] {S : AddSubgroup M} (hS : IsClosed (S : Set M)) {x : M} (hx : x ∈ S)
    {a : ℤ_[p]} (h : Tendsto (fun n ↦ a.appr n • x) atTop (𝓝 (a • x))) : a • x ∈ S :=
  hS.mem_of_tendsto h (Eventually.of_forall fun n ↦ S.nsmul_mem hx (a.appr n))

end Module

end OneUnits
