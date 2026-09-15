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
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Constructions

/-!
# `p`-adic powers of principal units

Let `K` be a complete ultrametric field with `‖p‖ < 1`, for instance a finite extension of `ℚ_p`,
the field `ℂ_[p]`, or the completion of a number field at a prime above `p`. The principal units,
or `1`-units, `oneUnits K = {u : Kˣ | ‖u - 1‖ < 1}` form a pro-`p` group: `u ^ (p ^ k) → 1`
(`IsUltrametricDist.tendsto_pow_pow_sub_one`). Hence a principal unit `x` has `p`-adic powers
`x ^ a = lim x ^ aₙ` for `a ∈ ℤ_p` and integers `aₙ → a`, and `Additive (oneUnits K)` is a
`ℤ_[p]`-module. Mathlib has no such module structure.

## Main definitions

* `oneUnits K`: the subgroup of `Kˣ` of principal units.
* `OneUnits.zpPow x a`: the `p`-adic power `x ^ a = lim x ^ (a.appr n)` of `x : K` by `a : ℤ_[p]`
  (junk value when the sequence does not converge, e.g. if `‖x - 1‖ ≥ 1`).
* `OneUnits.instModule`: the `ℤ_[p]`-module structure `a • u = u ^ a` on `Additive (oneUnits K)`.

## Main results

* `IsUltrametricDist.norm_mul_sub_one_lt`, `IsUltrametricDist.norm_inv_sub_one`: the open unit
  disc around `1` is a group.
* `IsUltrametricDist.norm_pow_pow_sub_one_le`: on the ball `‖u - 1‖ ≤ c ≤ 1` the `n ^ k`-th power
  map contracts towards `1` by the factor `max c ‖n‖` at each step, uniformly in `u`. Hence
  `IsUltrametricDist.tendsto_pow_pow_sub_one`: `u ^ (n ^ k) → 1` for a `1`-unit `u` when
  `‖n‖ < 1`.
* `OneUnits.tendsto_zpow_of_tendsto`: `x ^ cₙ → x ^ a` for any integers `cₙ → a` in `ℤ_p`.
* `OneUnits.zpPow_add`, `OneUnits.zpPow_mul`, `OneUnits.mul_zpPow`: the exponent rules.
* `OneUnits.norm_zpPow_sub_zpPow_le`, `OneUnits.continuous_zpPow`: `x ^ a` is `1`-Lipschitz in
  `x` and continuous in `a`. Hence the scalar action is continuous in both arguments:
  `OneUnits.continuous_smul_const` and the `ContinuousConstSMul ℤ_[p] (Additive (oneUnits K))`
  instance, so `Additive (oneUnits K)` is a topological `ℤ_[p]`-module.
* `OneUnits.natCast_smul`: natural `p`-adic powers are ordinary powers.
* `OneUnits.tendsto_appr_nsmul`, `OneUnits.tendsto_appr_nsmul_pi`: `a • u = lim (a.appr n) • u`
  on the module side, for one group of principal units and for a product of them.
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

theorem PadicInt.tendsto_appr {p : ℕ} [hp : Fact p.Prime] (a : ℤ_[p]) :
    Tendsto (fun n ↦ (a.appr n : ℤ_[p])) atTop (𝓝 a) := by
  have : ∀ n : ℕ, ‖((a.appr n : ℤ_[p]) - a)‖ ≤ ((p : ℝ)⁻¹) ^ n := fun n ↦ by
    calc _ ≤ (p : ℝ) ^ (-n : ℤ) := by simpa [norm_sub_rev] using
          (PadicInt.norm_le_pow_iff_mem_span_pow _ n).2 (PadicInt.appr_spec n a)
      _ = ((p : ℝ)⁻¹) ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
  simpa [tendsto_iff_norm_sub_tendsto_zero] using squeeze_zero (fun n ↦ norm_nonneg _) this
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)))

namespace IsUltrametricDist

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem norm_eq_one_of_norm_sub_one_lt_one {u : K} (hu : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  rw [← (add_sub_cancel 1 u), IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by grind [norm_one]),norm_one, max_eq_left hu.le]

theorem norm_mul_sub_one_lt {u v : K} (hu : ‖u - 1‖ < 1) (hv : ‖v - 1‖ < 1) :
    ‖u * v - 1‖ < 1 := by
  simpa [show u * v - 1 = (u - 1) * v + (v - 1) by ring] using lt_of_le_of_lt
    (IsUltrametricDist.norm_add_le_max _ _)
    (max_lt (by simpa [norm_mul, norm_eq_one_of_norm_sub_one_lt_one hv, mul_one]) hv)

theorem norm_inv_sub_one {u : K} (hu : ‖u - 1‖ < 1) : ‖u⁻¹ - 1‖ = ‖u - 1‖ := by
  have : u ≠ 0 := by aesop
  rw [show u⁻¹ - 1 = (1 - u) / u by grind, norm_div, norm_eq_one_of_norm_sub_one_lt_one hu,
    div_one, norm_sub_rev]

theorem norm_pow_sub_one_lt {u : K} (hu : ‖u - 1‖ < 1) (n : ℕ) : ‖u ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using norm_mul_sub_one_lt ih hu

theorem norm_pow_sub_pow_le {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  rw [← (Commute.all x y).geom_sum₂_mul n, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _)
    (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ ?_)
  simpa using mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hx) (by positivity)
    (pow_le_one₀ (norm_nonneg _) hy)

theorem norm_pow_sub_one_le {x : K} (hx : ‖x‖ ≤ 1) (n : ℕ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  simpa using norm_pow_sub_pow_le hx (norm_one (α := K)).le n

theorem norm_pow_sub_one_le_mul_max (n : ℕ) {u : K} (hu : ‖u - 1‖ ≤ 1) :
    ‖u ^ n - 1‖ ≤ ‖u - 1‖ * max ‖u - 1‖ ‖(n : K)‖ := by
  calc _ = ‖(∑ i ∈ Finset.range n, (u ^ i - 1)) + (n : K)‖ * ‖u - 1‖ := by
        rw [← norm_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one, sub_add_cancel, geom_sum_mul u n]
    _ ≤ max ‖u - 1‖ ‖(n : K)‖ * ‖u - 1‖ := by
        refine mul_le_mul_of_nonneg_right ((IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le_max ?_ le_rfl)) (norm_nonneg _)
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
          fun i _ ↦ norm_pow_sub_one_le ?_ i
        rw [← sub_add_cancel u 1]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu (by simp))
    _ = _ := mul_comm _ _

theorem norm_pow_pow_sub_one_le (n k : ℕ) {c : ℝ} (hc : c ≤ 1) {u : K} (hu : ‖u - 1‖ ≤ c) :
    ‖u ^ n ^ k - 1‖ ≤ max c ‖(n : K)‖ ^ k * c := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    have h : max c ‖(n : K)‖ ^ k * c ≤ c :=
      mul_le_of_le_one_left ((norm_nonneg _).trans hu) (pow_le_one₀ (le_max_of_le_left
        ((norm_nonneg _).trans hu)) (max_le hc (IsUltrametricDist.norm_natCast_le_one K n)))
    calc _ = _ := by rw [pow_succ, pow_mul]
      _ ≤ _ := norm_pow_sub_one_le_mul_max n (ih.trans (h.trans hc))
      _ ≤ _ := mul_le_mul ih (max_le_max (ih.trans h) le_rfl)
        (le_max_of_le_left (norm_nonneg _)) (by positivity [(norm_nonneg _).trans hu])
      _ = _ := by ring

theorem tendsto_pow_pow_sub_one {n : ℕ} (hn : ‖(n : K)‖ < 1) {u : K} (hu : ‖u - 1‖ < 1) :
    Tendsto (fun k : ℕ ↦ u ^ n ^ k - 1) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun k ↦ norm_pow_pow_sub_one_le n k hu.le le_rfl) ?_
  rw [← zero_mul ‖u - 1‖]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_of_le_left (norm_nonneg _))
    (max_lt hu hn)).mul_const _

theorem norm_zpow_sub_one_le {x : K} (hx : ‖x - 1‖ < 1) (n : ℤ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using norm_pow_sub_one_le (norm_eq_one_of_norm_sub_one_lt_one hx).le m
  · simpa [norm_inv_sub_one (norm_pow_sub_one_lt hx m)] using
    norm_pow_sub_one_le (norm_eq_one_of_norm_sub_one_lt_one hx).le m

theorem norm_div_sub_one {x y : K} (hy : ‖y - 1‖ < 1) : ‖x / y - 1‖ = ‖x - y‖ := by
  rw [div_sub_one (by aesop), norm_div, norm_eq_one_of_norm_sub_one_lt_one hy, div_one]

theorem norm_sub_lt_one {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) : ‖x - y‖ < 1 :=
  calc _ = ‖(x - 1) + - (y - 1)‖ := by ring_nf
    _ ≤ max ‖x - 1‖ ‖-(y - 1)‖ := IsUltrametricDist.norm_add_le_max _ _
    _ < 1 := by simpa only [norm_neg] using max_lt hx hy

theorem norm_zpow_sub_zpow_le {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) (n : ℤ) :
    ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  have : x ^ n - y ^ n = y ^ n * ((x / y) ^ n - 1) := by
    rw [div_zpow, mul_sub, mul_one, mul_div_cancel₀ _ (zpow_ne_zero _ (by aesop))]
  simpa [this, norm_eq_one_of_norm_sub_one_lt_one hy, ← norm_div_sub_one hy] using
    norm_zpow_sub_one_le (by simpa [norm_div_sub_one hy] using norm_sub_lt_one hx hy) n

end IsUltrametricDist

open IsUltrametricDist

/-- The principal units, or `1`-units, of an ultrametric normed field: the units `u` with
`‖u - 1‖ < 1`. [Con, p. 27]. -/
def oneUnits (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] : Subgroup Kˣ where
  carrier := {u | ‖(u : K) - 1‖ < 1}
  mul_mem' hu hv := norm_mul_sub_one_lt hu hv
  one_mem' := by simp
  inv_mem' {u} hu := by simpa [norm_inv_sub_one hu]

namespace OneUnits

@[simp]
theorem mem_oneUnits_iff {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {u : Kˣ} :
    u ∈ oneUnits K ↔ ‖(u : K) - 1‖ < 1 := Iff.rfl

section ZpPow

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [Fact (‖((p : ℕ) : K)‖ < 1)]

omit [Fact p.Prime] [CompleteSpace K] in
theorem exists_forall_norm_zpow_sub_one_lt {x : K} (hx : ‖x - 1‖ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ m : ℤ, (p : ℤ) ^ k ∣ m → ‖x ^ m - 1‖ < ε := by
  obtain ⟨k, hk⟩ := Metric.tendsto_atTop.1 (tendsto_pow_pow_sub_one (n := p) Fact.out hx) ε hε
  refine ⟨k, fun m ⟨j, hj⟩ ↦ ?_⟩
  calc ‖x ^ m - 1‖ = ‖(x ^ ((p : ℤ) ^ k)) ^ j - 1‖ := by rw [← zpow_mul, ← hj]
    _ ≤ ‖x ^ ((p : ℤ) ^ k) - 1‖ := by
        refine norm_zpow_sub_one_le ?_ j
        rw [← Int.natCast_pow, zpow_natCast]
        exact norm_pow_sub_one_lt hx _
    _ < ε := by
      rw [← Int.natCast_pow, zpow_natCast]
      aesop

omit [CompleteSpace K] in
theorem tendsto_zpow_of_tendsto_zero {x : K} (hx : ‖x - 1‖ < 1) {c : ℕ → ℤ}
    (hc : Tendsto (fun n ↦ (c n : ℤ_[p])) atTop (𝓝 0)) :
    Tendsto (fun n ↦ x ^ c n) atTop (𝓝 1) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_forall_norm_zpow_sub_one_lt (p := p) hx hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hc _ (zpow_pos (a := (p : ℝ))
    (by exact_mod_cast (Fact.out : p.Prime).pos) (-k : ℤ))
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa [dist_eq_norm] using hk _ (mod_cast PadicInt.norm_int_le_pow_iff_dvd.1
    (dist_zero_right (c n : ℤ_[p]) ▸ hN n hn).le)


omit [CompleteSpace K] in
theorem cauchySeq_pow_appr {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) :
    CauchySeq fun n ↦ x ^ a.appr n := by
  refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_forall_norm_zpow_sub_one_lt (p := p) hx hε
  refine ⟨k, fun n hn ↦ ?_⟩
  obtain ⟨_, hd⟩ := Nat.exists_eq_add_of_le (PadicInt.appr_mono a hn)
  rw [dist_eq_norm, hd, pow_add, ← mul_sub_one, norm_mul, norm_pow,
    norm_eq_one_of_norm_sub_one_lt_one hx, one_pow, one_mul, ← zpow_natCast]
  exact hk _ (by simpa [hd] using Int.natCast_dvd_natCast.2 (PadicInt.dvd_appr_sub_appr a k n hn))

/-- The `p`-adic power `x ^ a = lim x ^ (a.appr n)` of `x : K` by `a : ℤ_[p]`. This is the limit
of [Klo, Exercise 6.1 (d)] and [BG, p. 4], with `a.appr n` as the approximating integers. The
value is junk unless the sequence converges, which it does when `‖x - 1‖ < 1`
(`tendsto_pow_appr`). -/
noncomputable
def zpPow (x : K) (a : ℤ_[p]) : K := limUnder atTop fun n ↦ x ^ a.appr n

theorem tendsto_pow_appr {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) :
    Tendsto (fun n ↦ x ^ a.appr n) atTop (𝓝 (zpPow x a)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_pow_appr hx a))

theorem tendsto_zpow_of_tendsto {x : K} (hx : ‖x - 1‖ < 1) {c : ℕ → ℤ} {a : ℤ_[p]}
    (hc : Tendsto (fun n ↦ (c n : ℤ_[p])) atTop (𝓝 a)) :
    Tendsto (fun n ↦ x ^ c n) atTop (𝓝 (zpPow x a)) := by
  simpa [← zpow_natCast, ← zpow_add₀ (a := x) (by aesop)] using (tendsto_pow_appr hx a).mul
    (tendsto_zpow_of_tendsto_zero (c := fun n ↦ c n - a.appr n) hx
      (by simpa using hc.sub (PadicInt.tendsto_appr a)))

theorem zpPow_intCast {x : K} (hx : ‖x - 1‖ < 1) (n : ℤ) : zpPow x (n : ℤ_[p]) = x ^ n :=
  tendsto_nhds_unique (tendsto_zpow_of_tendsto (p := p) hx (c := fun _ ↦ n) tendsto_const_nhds)
    tendsto_const_nhds

theorem zpPow_natCast {x : K} (hx : ‖x - 1‖ < 1) (n : ℕ) : zpPow x (n : ℤ_[p]) = x ^ n := by
  rw [← Int.cast_natCast, zpPow_intCast hx (n : ℤ), zpow_natCast]

@[simp]
theorem zpPow_zero {x : K} (hx : ‖x - 1‖ < 1) : zpPow x (0 : ℤ_[p]) = 1 := by
  simpa using zpPow_intCast hx 0

@[simp]
theorem zpPow_one {x : K} (hx : ‖x - 1‖ < 1) : zpPow x (1 : ℤ_[p]) = x := by
  simpa using zpPow_intCast hx 1

@[simp]
theorem one_zpPow (a : ℤ_[p]) : zpPow (1 : K) a = 1 :=
  tendsto_nhds_unique (tendsto_pow_appr (p := p) (by simp) a) (by simp)

/-- `g ^ (λ + μ) = g ^ λ * g ^ μ` [Klo, Exercise 6.1 (d)]. Compute the limit along
`a.appr n + b.appr n`, which also tends to `a + b`. -/
theorem zpPow_add {x : K} (hx : ‖x - 1‖ < 1) (a b : ℤ_[p]) :
    zpPow x (a + b) = zpPow x a * zpPow x b := by
  have : Tendsto (fun n ↦ (((a.appr n : ℤ) + (b.appr n : ℤ) : ℤ) : ℤ_[p])) atTop (𝓝 (a + b)) :=
    ((PadicInt.tendsto_appr a).add (PadicInt.tendsto_appr b)).congr fun n ↦ by aesop
  refine tendsto_nhds_unique ((tendsto_zpow_of_tendsto hx this).congr fun n ↦ ?_)
    ((tendsto_pow_appr hx a).mul (tendsto_pow_appr hx b))
  rw [zpow_add₀ (by aesop), zpow_natCast, zpow_natCast]

/-- `(g h) ^ λ = g ^ λ * h ^ λ` for commuting `g, h` [Klo, Exercise 6.1 (d)]: the "sufficient
condition" of the exercise is automatic in a field. -/
theorem mul_zpPow {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) (a : ℤ_[p]) :
    zpPow (x * y) a = zpPow x a * zpPow y a := by
  refine tendsto_nhds_unique (tendsto_pow_appr (norm_mul_sub_one_lt hx hy) a) ?_
  simpa only [mul_pow] using (tendsto_pow_appr hx a).mul (tendsto_pow_appr hy a)

/-- `p`-adic powers stay in the closed ball of radius `‖x - 1‖` around `1`: the bound
`norm_pow_sub_one_le` passes to the limit. This is the image of `ℤ_[p] → cl⟨x⟩` of
[Klo, Exercise 6.1 (e)]. -/
theorem norm_zpPow_sub_one_le {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) :
    ‖zpPow x a - 1‖ ≤ ‖x - 1‖ :=
  le_of_tendsto (((tendsto_pow_appr hx a).sub_const 1).norm) <| Eventually.of_forall fun _ ↦
    norm_pow_sub_one_le (norm_eq_one_of_norm_sub_one_lt_one hx).le _

theorem norm_zpPow_sub_one_lt {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) :
    ‖zpPow x a - 1‖ < 1 :=
  (norm_zpPow_sub_one_le hx a).trans_lt hx

@[simp]
theorem norm_zpPow {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) : ‖zpPow x a‖ = 1 :=
  norm_eq_one_of_norm_sub_one_lt_one (norm_zpPow_sub_one_lt hx a)

theorem zpPow_ne_zero {x : K} (hx : ‖x - 1‖ < 1) (a : ℤ_[p]) : zpPow x a ≠ 0 :=
  norm_pos_iff.1 ((norm_zpPow hx a) ▸ one_pos)

/-- `x ↦ x ^ a` is `1`-Lipschitz on the principal units: `norm_pow_sub_pow_le` in the limit. -/
theorem norm_zpPow_sub_zpPow_le {x y : K} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) (a : ℤ_[p]) :
    ‖zpPow x a - zpPow y a‖ ≤ ‖x - y‖ :=
  le_of_tendsto (((tendsto_pow_appr hx a).sub (tendsto_pow_appr hy a)).norm) <|
    Eventually.of_forall fun _ ↦ norm_pow_sub_pow_le (norm_eq_one_of_norm_sub_one_lt_one hx).le
    (norm_eq_one_of_norm_sub_one_lt_one hy).le _

theorem zpPow_mul {x : K} (hx : ‖x - 1‖ < 1) (a b : ℤ_[p]) :
    zpPow x (a * b) = zpPow (zpPow x b) a := by
  have : Tendsto (fun n ↦ (((a.appr n : ℤ) * (b.appr n : ℤ) : ℤ) : ℤ_[p])) atTop (𝓝 (a * b)) :=
    ((PadicInt.tendsto_appr a).mul (PadicInt.tendsto_appr b)).congr fun n ↦ (by aesop)
  have : Tendsto (fun n ↦ (x ^ b.appr n) ^ a.appr n) atTop (𝓝 (zpPow x (a * b))) := by
    refine (tendsto_zpow_of_tendsto hx this).congr fun n ↦ ?_
    rw [← pow_mul, ← zpow_natCast x (b.appr n * a.appr n)]
    grind
  have h : Tendsto (fun n ↦ (x ^ b.appr n) ^ a.appr n) atTop (𝓝 (zpPow (zpPow x b) a)) :=
    (tendsto_pow_appr (norm_zpPow_sub_one_lt hx b) a).congr_dist <|
      squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (dist_eq_norm _ _).trans_le <|
      norm_pow_sub_pow_le (norm_zpPow hx b).le (by simp [norm_eq_one_of_norm_sub_one_lt_one hx]) _)
      (by simpa using ((tendsto_pow_appr hx b).const_sub (zpPow x b)).norm)
  exact tendsto_nhds_unique this h

theorem norm_zpPow_sub_one_le_of_dvd {x : K} (hx : ‖x - 1‖ < 1) {a : ℤ_[p]} {k : ℕ}
    (h : (p : ℤ_[p]) ^ k ∣ a) : ‖zpPow x a - 1‖ ≤ ‖x ^ p ^ k - 1‖ := by
  obtain ⟨d, rfl⟩ := h
  simpa [mul_comm, zpPow_mul hx, ← Nat.cast_pow, zpPow_natCast hx] using norm_zpPow_sub_one_le
    (norm_pow_sub_one_lt hx _) d

theorem continuous_zpPow {x : K} (hx : ‖x - 1‖ < 1) : Continuous fun a : ℤ_[p] ↦ zpPow x a := by
  refine Metric.continuous_iff.2 fun b ε hε ↦ ?_
  obtain ⟨k, hk⟩ := exists_forall_norm_zpow_sub_one_lt (p := p) hx hε
  refine ⟨(p : ℝ) ^ (-k : ℤ), zpow_pos (mod_cast (Fact.out : p.Prime).pos) _, fun a ha ↦ ?_⟩
  rw [dist_eq_norm] at ha ⊢
  rw [← norm_div_sub_one (norm_zpPow_sub_one_lt hx b), ← sub_add_cancel a b, zpPow_add hx,
    mul_div_cancel_right₀ _ (zpPow_ne_zero hx b)]
  refine (norm_zpPow_sub_one_le_of_dvd hx (Ideal.mem_span_singleton.1
    ((PadicInt.norm_le_pow_iff_mem_span_pow (a - b) k).1 ha.le))).trans_lt ?_
  simpa only [zpow_natCast] using hk ((p ^ k : ℕ) : ℤ) (by simp)

end ZpPow

section Module

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [Fact (‖((p : ℕ) : K)‖ < 1)]

/-- The `p`-adic power of a principal unit, as a principal unit. -/
noncomputable
def zpPowUnit (u : oneUnits K) (a : ℤ_[p]) : oneUnits K :=
  ⟨Units.mk0 (zpPow ((u : Kˣ) : K) a) (zpPow_ne_zero (mem_oneUnits_iff.1 u.2) a),
    mem_oneUnits_iff.2 (norm_zpPow_sub_one_lt (mem_oneUnits_iff.1 u.2) a)⟩

noncomputable
instance instSMul : SMul ℤ_[p] (Additive (oneUnits K)) :=
  ⟨fun a u ↦ Additive.ofMul (zpPowUnit u.toMul a)⟩

@[simp]
theorem coe_smul (a : ℤ_[p]) (u : Additive (oneUnits K)) :
    (((a • u).toMul : Kˣ) : K) = zpPow ((u.toMul : Kˣ) : K) a := rfl

omit [CompleteSpace K] in
theorem ext_of_coe {u v : Additive (oneUnits K)} (h : ((u.toMul : Kˣ) : K) = ((v.toMul : Kˣ) : K)) :
  u = v := Additive.toMul.injective (Subtype.ext (Units.ext h))

/-- The `ℤ_[p]`-module structure `a • u = u ^ a` on the principal units. "Regard `G` as a
finitely generated `ℤ_p`-module" [Klo, Exercise 6.1 (f)]; the six axioms are the exponent rules
`zpPow_one`, `zpPow_mul`, `one_zpPow`, `mul_zpPow`, `zpPow_add`, `zpPow_zero` of
[Klo, Exercise 6.1 (d)], read additively. -/
noncomputable
instance instModule : Module ℤ_[p] (Additive (oneUnits K)) where
  one_smul u := ext_of_coe <| by
    simpa [coe_smul] using zpPow_one (mem_oneUnits_iff.1 u.toMul.2)
  mul_smul a b u := ext_of_coe <| by
    simpa [coe_smul, coe_smul, coe_smul] using zpPow_mul (mem_oneUnits_iff.1 u.toMul.2) a b
  smul_zero a := ext_of_coe <| by simp [coe_smul]
  smul_add a u v := ext_of_coe <| by
    rw [coe_smul, toMul_add, Subgroup.coe_mul, Units.val_mul,
      mul_zpPow (mem_oneUnits_iff.1 u.toMul.2) (mem_oneUnits_iff.1 v.toMul.2) a]
    rfl
  add_smul a b u := ext_of_coe <| by
    rw [coe_smul, zpPow_add (mem_oneUnits_iff.1 u.toMul.2) a b]
    rfl
  zero_smul u := ext_of_coe <| by
    simpa [coe_smul] using zpPow_zero (mem_oneUnits_iff.1 u.toMul.2)

theorem natCast_smul (n : ℕ) (u : Additive (oneUnits K)) : (n : ℤ_[p]) • u = n • u :=
  ext_of_coe (by simp [zpPow_natCast (mem_oneUnits_iff.1 u.toMul.2)])

omit [CompleteSpace K] [Fact (‖((p : ℕ) : K)‖ < 1)] in
theorem isInducing_coe :
    Topology.IsInducing (fun u : Additive (oneUnits K) ↦ ((u.toMul : Kˣ) : K)) :=
  Units.isEmbedding_val₀.isInducing.comp Topology.IsInducing.subtypeVal

theorem tendsto_appr_nsmul (a : ℤ_[p]) (u : Additive (oneUnits K)) :
    Tendsto (fun n ↦ a.appr n • u) atTop (𝓝 (a • u)) := by
  rw [isInducing_coe.tendsto_nhds_iff]
  have hu : ‖((u.toMul : Kˣ) : K) - 1‖ < 1 := mem_oneUnits_iff.1 u.toMul.2
  refine (tendsto_pow_appr (p := p) hu a).congr fun n ↦ ?_
  rw [Function.comp_apply, ← natCast_smul (p := p) (a.appr n) u, coe_smul, zpPow_natCast hu]

theorem tendsto_appr_nsmul_pi {ι : Type*} {F : ι → Type*}
    [∀ i, NontriviallyNormedField (F i)] [∀ i, IsUltrametricDist (F i)]
    [∀ i, CompleteSpace (F i)] [∀ i, Fact (‖((p : ℕ) : F i)‖ < 1)]
    (a : ℤ_[p]) (x : ∀ i, Additive (oneUnits (F i))) :
    Tendsto (fun n ↦ a.appr n • x) atTop (𝓝 (a • x)) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_appr_nsmul a (x i)

theorem continuous_smul_const (u : Additive (oneUnits K)) :
    Continuous fun a : ℤ_[p] ↦ a • u := by
  simpa [isInducing_coe.continuous_iff] using (continuous_zpPow
    (mem_oneUnits_iff.1 u.toMul.2)).congr fun a ↦ by simp

/-- `x ↦ x ^ a` is continuous on the open unit ball around `1`, being `1`-Lipschitz there
(`norm_zpPow_sub_zpPow_le`). -/
theorem continuousOn_zpPow (a : ℤ_[p]) :
    ContinuousOn (fun x : K ↦ zpPow x a) {x : K | ‖x - 1‖ < 1} := by
  refine Metric.continuousOn_iff.2 fun x hx ε hε ↦ ⟨ε, hε, fun y hy hdist ↦ ?_⟩
  rw [dist_eq_norm] at hdist ⊢
  exact lt_of_le_of_lt (norm_zpPow_sub_zpPow_le hy hx a) hdist

instance : ContinuousConstSMul ℤ_[p] (Additive (oneUnits K)) where
  continuous_const_smul a := by
    simpa [isInducing_coe.continuous_iff] using ((continuousOn_zpPow (K := K) a).comp_continuous
      isInducing_coe.continuous fun u ↦ mem_oneUnits_iff.1 u.toMul.2).congr fun u ↦ (by simp)

/-- A closed subgroup of a `ℤ_[p]`-module in which `a • x = lim (a.appr n) • x` is a
`ℤ_[p]`-submodule. -/
theorem _root_.AddSubgroup.smul_mem_of_isClosed {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] {S : AddSubgroup M} (hS : IsClosed (S : Set M)) {x : M} (hx : x ∈ S)
    {a : ℤ_[p]} (h : Tendsto (fun n ↦ a.appr n • x) atTop (𝓝 (a • x))) : a • x ∈ S :=
  hS.mem_of_tendsto h (Eventually.of_forall fun n ↦ S.nsmul_mem hx (a.appr n))

end Module

end OneUnits
