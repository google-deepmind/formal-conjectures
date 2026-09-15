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
public import FormalConjecturesForMathlib.Analysis.Normed.Algebra.Logarithm
public import FormalConjecturesForMathlib.NumberTheory.Padics.OneUnits
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# The Iwasawa `p`-adic logarithm

Iwasawa's extension of the `p`-adic logarithm to those `x` in a complete ultrametric field `K` of
characteristic zero some positive power of which is a `1`-unit times a power of `p` — which in
`K = ℂ_[p]` is every nonzero element. It is built on `NormedSpace.log`, the series
`log u = ∑ₙ ((-1) ^ (n + 1) / n) • (u - 1) ^ n` vendored from
[mathlib#43670](https://github.com/leanprover-community/mathlib4/pull/43670) as
`FormalConjecturesForMathlib.Analysis.Normed.Algebra.Logarithm`, through the normalisation
`log_p x = log (x ^ N / p ^ m) / N`. That pull request lists this extension, the "analytic
continuation of `log` in the ultrametric case" with `log p = 0`, as future work.

## Main definitions

* `HasIwasawaLog p x`: some power `x ^ N` (`N ≥ 1`) is a `1`-unit times a power of `p`.
* `iwasawaLog p`: the Iwasawa logarithm `NormedSpace.log (x ^ N / p ^ m) / N` on
  `HasIwasawaLog p`, characterised by being a homomorphism with `log p = 0`.

## Main results

* `PadicComplex.hasIwasawaLog_iff`: every nonzero element of `ℂ_[p]` has an Iwasawa logarithm.

## Scope

This file carries only what `FormalConjectures.Paper.GrossKuzmin` uses: `iwasawaLog` is the
`log_p` of Gross's regulator map, and `hasIwasawaLog_iff` is what shows that no junk value of
`iwasawaLog` is involved there. The analytic theory is deliberately omitted, as it is in
mathlib#43670: that `NormedSpace.log` converges on `‖u - 1‖ < 1` and turns products into sums
there, and hence that `iwasawaLog` is independent of the choice of `N` and `m` below and is a
homomorphism with `log p = 0`. The ultrametric estimates on `1`-units are those of
`FormalConjecturesForMathlib.NumberTheory.Padics.OneUnits`.

## References

* [Wiki] Wikipedia, *p-adic exponential function* (the Iwasawa logarithm).
-/

@[expose] public section

namespace PadicIwasawaLog

variable {p : ℕ}

/-! ### The Iwasawa logarithm: its domain, and its definition -/

section Iwasawa

variable {K : Type*} [NontriviallyNormedField K]

/-- `HasPrincipalUnitPow u` says that some positive power of `u` is a `1`-unit, `‖u ^ m - 1‖ < 1`.
-/
def HasPrincipalUnitPow (u : K) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ‖u ^ m - 1‖ < 1

variable (p) in
/-- `HasIwasawaLog p x` says that some positive power of `x` is a `1`-unit times a power of `p`:
`‖x ^ N / p ^ m - 1‖ < 1` for some `N ≥ 1` and `m : ℤ`. -/
def HasIwasawaLog (x : K) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ m : ℤ, ‖x ^ N / ((p : ℕ) : K) ^ m - 1‖ < 1

variable (p) in
/-- The **Iwasawa logarithm**: the unique extension of `NormedSpace.log` from the `1`-units to
`HasIwasawaLog p` (all of `ℂ_p^×` when `K = ℂ_p`) which is a homomorphism and has `log p = 0`
[Wiki]. Concretely `iwasawaLog p x = NormedSpace.log (x ^ N / p ^ m) / N` for `N ≥ 1`, `m` with
`‖x ^ N / p ^ m - 1‖ < 1`; the value is independent of that choice, though this file does not
prove it, and to fix a value here `N` is taken least and `m` by choice. Junk value `0` outside
the domain. -/
noncomputable def iwasawaLog (x : K) : K := by
  classical
  exact if h : ∃ N : ℕ, 0 < N ∧ ∃ m : ℤ, ‖x ^ N / ((p : ℕ) : K) ^ m - 1‖ < 1 then
    NormedSpace.log (x ^ Nat.find h / ((p : ℕ) : K) ^ Classical.choose (Nat.find_spec h).2) /
      (Nat.find h : K)
  else 0

theorem HasIwasawaLog.of_norm_sub_one_lt {u : K} (hu : ‖u - 1‖ < 1) : HasIwasawaLog p u :=
  ⟨1, one_pos, 0, by simpa using hu⟩

theorem HasIwasawaLog.ne_zero {x : K} (hx : HasIwasawaLog p x) : x ≠ 0 := by
  obtain ⟨N, hN, m, h⟩ := hx
  intro rfl
  simp [zero_pow hN.ne'] at h

theorem HasIwasawaLog.mul [hp : Fact p.Prime] [IsUltrametricDist K] [CharZero K] {x y : K}
    (hx : HasIwasawaLog p x) (hy : HasIwasawaLog p y) : HasIwasawaLog p (x * y) := by
  obtain ⟨N, hN, m, h⟩ := hx
  obtain ⟨N', hN', m', h'⟩ := hy
  refine ⟨N * N', Nat.mul_pos hN hN', m * N' + m' * N, ?_⟩
  calc _ = ‖(x ^ N / ((p : ℕ) : K) ^ m) ^ N' * (y ^ N' / ((p : ℕ) : K) ^ m') ^ N - 1‖ := by
        simp [zpow_add₀, hp.out.ne_zero, zpow_mul]; ring_nf
       _ < 1 := IsUltrametricDist.norm_mul_sub_one_lt (IsUltrametricDist.norm_pow_sub_one_lt h N')
        (IsUltrametricDist.norm_pow_sub_one_lt h' N)

theorem HasIwasawaLog.map {L : Type*} [NontriviallyNormedField L] (f : K →+* L)
    (hf : ∀ y : K, ‖f y‖ = ‖y‖) {x : K} (hx : HasIwasawaLog p x) : HasIwasawaLog p (f x) := by
  obtain ⟨N, hN, m, h⟩ := hx
  refine ⟨N, hN, m, ?_⟩
  simpa only [← map_natCast f, ← map_zpow₀, ← map_pow, ← map_div₀, ← map_one f, ← map_sub, hf]

end Iwasawa

/-! ### Instantiation on `ℚ_p`-bar and `ℂ_p` -/

section PadicComplex

variable [hp : Fact p.Prime]

theorem PadicAlgCl.norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]

theorem PadicComplex.norm_natCast_p_lt_one : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  simpa [← PadicComplex.coe_natCast, PadicComplex.norm_extends, PadicAlgCl.norm_natCast_p] using
    inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem PadicAlgCl.exists_norm_pow_div_zpow_eq_one {y : PadicAlgCl p} (hy : y ≠ 0) :
    ∃ b : ℕ, 0 < b ∧ ∃ a : ℤ, ‖y ^ b / ((p : ℕ) : PadicAlgCl p) ^ a‖ = 1 := by
  set n := (minpoly ℚ_[p] y).natDegree with hn_def
  set a₀ := (minpoly ℚ_[p] y).coeff 0 with ha₀_def
  refine ⟨n, minpoly.natDegree_pos (Algebra.IsAlgebraic.isAlgebraic y).isIntegral, a₀.valuation, ?_⟩
  rw [norm_div, norm_pow, norm_zpow, ← PadicAlgCl.spectralNorm_eq,
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel (mod_cast (minpoly.natDegree_pos
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral).ne'), Real.rpow_one,
    Padic.norm_eq_zpow_neg_valuation (minpoly.coeff_zero_ne_zero
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral hy), PadicAlgCl.norm_natCast_p, inv_zpow',
    div_self (zpow_ne_zero _ (mod_cast (hp.out.pos).ne'))]

theorem PadicAlgCl.hasPrincipalUnitPow_of_norm_eq_one {u : PadicAlgCl p} (hu : ‖u‖ = 1) :
    HasPrincipalUnitPow u := by
  set S : Submodule ℚ_[p] (PadicAlgCl p) := Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] {u})
  have : FiniteDimensional ℚ_[p] S := Module.Finite.iff_fg.2
    (Algebra.IsAlgebraic.isAlgebraic u).isIntegral.fg_adjoin_singleton
  have : ProperSpace S := FiniteDimensional.proper ℚ_[p] S
  set s : ℕ → S := fun k => ⟨u ^ k,
    Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] u) k⟩ with hs_def
  have : ∀ k, s k ∈ Metric.closedBall (0 : S) 1 := fun _ ↦ by aesop
  obtain ⟨L, -, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : S) 1).tendsto_subseq this
  obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.1 hlim (1 / 2) (by norm_num)
  refine ⟨ψ (k₀ + 1) - ψ k₀, Nat.sub_pos_of_lt (hψ (Nat.lt_succ_self _)), ?_⟩
  calc _ = ‖u ^ ψ (k₀ + 1) - u ^ ψ k₀‖ := by
        rw [← Nat.add_sub_cancel' (hψ (Nat.lt_succ_self _)).le, pow_add, ← mul_sub_one, norm_mul,
          norm_pow, hu, one_pow, one_mul, Nat.succ_eq_add_one, add_tsub_cancel_left]
       _ = dist (s (ψ (k₀ + 1))) (s (ψ k₀)) := by
        rw [dist_eq_norm, Submodule.coe_norm, Submodule.coe_sub]
       _ ≤ dist (s (ψ (k₀ + 1))) L + dist (s (ψ k₀)) L := dist_triangle_right _ _ _
       _ < 1 / 2 + 1 / 2 := add_lt_add (hk₀ _ (Nat.le_succ _)) (hk₀ _ le_rfl)
       _ = 1 := by norm_num

theorem PadicAlgCl.hasIwasawaLog {y : PadicAlgCl p} (hy : y ≠ 0) : HasIwasawaLog p y := by
  obtain ⟨b, hb, a, h1⟩ := PadicAlgCl.exists_norm_pow_div_zpow_eq_one hy
  obtain ⟨N, hN, h2⟩ := PadicAlgCl.hasPrincipalUnitPow_of_norm_eq_one h1
  exact ⟨b * N, Nat.mul_pos hb hN, a * N, by rwa [pow_mul, zpow_mul, zpow_natCast, ← div_pow]⟩

theorem PadicComplex.exists_norm_sub_coe_lt {x : ℂ_[p]} (hx : x ≠ 0) :
    ∃ y : PadicAlgCl p, ‖x - y‖ < ‖x‖ := by
  obtain ⟨_, ⟨y, rfl⟩, hd⟩ := Metric.mem_closure_iff.1
    (UniformSpace.Completion.denseRange_coe x) ‖x‖ (norm_pos_iff.2 hx)
  exact ⟨y, by rwa [dist_eq_norm] at hd⟩

/-- **The Iwasawa logarithm is defined on all of `ℂ_p^×`** [Wiki]: `x = y · (x / y)` with `y`
algebraic and `x / y` a `1`-unit. -/
theorem PadicComplex.hasIwasawaLog {x : ℂ_[p]} (hx : x ≠ 0) : HasIwasawaLog p x := by
  obtain ⟨y, hy⟩ := PadicComplex.exists_norm_sub_coe_lt hx
  have e : (y : ℂ_[p]) * (x / y) = x := by rw [mul_comm, div_mul_cancel₀ _ (by aesop)]
  rw [show x = y * (x / y) by rw [mul_comm, div_mul_cancel₀ _ (by aesop)]]
  refine ((PadicAlgCl.hasIwasawaLog (by aesop)).map (algebraMap (PadicAlgCl p) ℂ_[p])
    (PadicComplex.norm_extends p)).mul (HasIwasawaLog.of_norm_sub_one_lt ?_)
  rw [div_sub_one (by aesop), norm_div, div_lt_one (by aesop)]
  simpa using hy.trans_eq (IsUltrametricDist.norm_eq_of_add_norm_lt_max (y := -(y : ℂ_[p]))
    (by simp [← sub_eq_add_neg, hy]))

theorem PadicComplex.hasIwasawaLog_iff {x : ℂ_[p]} : HasIwasawaLog p x ↔ x ≠ 0 :=
  ⟨HasIwasawaLog.ne_zero, PadicComplex.hasIwasawaLog⟩

end PadicComplex

end PadicIwasawaLog
