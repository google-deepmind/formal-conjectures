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
public import Mathlib
public import FormalConjecturesForMathlib.Leopoldt.NumberTheory.NumberField.EmbeddingsBasis
public import FormalConjecturesForMathlib.Leopoldt.NumberTheory.NumberField.Units
public import FormalConjecturesForMathlib.Leopoldt.NumberTheory.Padics.ExpLog

/-!
# Embeddings of a number field into `ℂ_[p]`

The size of the conjugates `σ x` of an algebraic integer, for `σ : K → ℂ_[p]`, against
divisibility by powers of `p`: an integer is divisible by a large power of `p` exactly when all
its conjugates are small. Also that every global unit has a principal-unit power at every such
embedding, which is what makes its Iwasawa logarithm defined.

Staging area: kept in the `Leopoldt` namespace. Narrow the imports and pick final namespaces
before upstreaming.
-/

@[expose] public section

open Filter NumberField

open scoped NumberField

namespace Leopoldt

section Implicit

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

/--
An algebraic integer whose conjugates in $\mathbb{C}_p$ are all small is divisible by a large
power of $p$: if $\sigma(y_n) \to 0$ for every embedding $\sigma : K \to \mathbb{C}_p$, then
$p^M \mid y_n$ for all large $n$, for every $M$.

The coordinates of $y_n$ in an integral basis are integers bounded by a fixed multiple of
$\max_\sigma \|\sigma(y_n)\|$ (`NumberField.exists_norm_repr_le`), and an integer of $p$-adic
absolute value at most $p^{-M}$ is divisible by $p^M$.
-/
theorem eventually_pow_dvd_of_tendsto_map {y : ℕ → 𝓞 K}
    (hy : ∀ σ : K →+* ℂ_[p], Tendsto (fun n ↦ σ (y n : K)) atTop (nhds 0)) (M : ℕ) :
    ∀ᶠ n in atTop, (p : 𝓞 K) ^ M ∣ y n := by
  classical
  obtain ⟨C, hC⟩ := NumberField.exists_norm_repr_le (E := ℂ_[p]) (integralBasis K)
  -- The vector of conjugates of `y n` tends to `0`, hence so does each integer coordinate.
  have hvec : Tendsto (fun n ↦ ‖fun σ : K →+* ℂ_[p] ↦ σ (y n : K)‖) atTop (nhds 0) := by
    simpa using (tendsto_pi_nhds.2 hy).norm
  have hcast : ∀ k : ℤ, ‖algebraMap ℚ ℂ_[p] (k : ℚ)‖ = ‖(k : ℚ_[p])‖ := by
    intro k
    rw [map_intCast, ← PadicComplex.norm_extends' p (k : ℚ_[p])]
    congr 1
    rw [map_intCast, PadicComplex.coe_eq, map_intCast]
  have hcoord : ∀ i, Tendsto
      (fun n ↦ ‖((((RingOfIntegers.basis K).repr (y n) i : ℤ) : ℚ_[p]))‖) atTop (nhds 0) := by
    intro i
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (by simpa using hvec.const_mul C)
    calc ‖((((RingOfIntegers.basis K).repr (y n) i : ℤ) : ℚ_[p]))‖
        = ‖algebraMap ℚ ℂ_[p] ((integralBasis K).repr (y n : K) i)‖ := by
          rw [integralBasis_repr_apply, eq_intCast, hcast]
      _ ≤ C * ‖fun σ : K →+* ℂ_[p] ↦ σ (y n : K)‖ := hC _ i
  -- Each coordinate is eventually divisible by `p ^ M`, hence so is `y n`.
  have hdvd : ∀ᶠ n in atTop, ∀ i, ((p : ℤ) ^ M) ∣ ((RingOfIntegers.basis K).repr (y n) i) := by
    rw [eventually_all]
    intro i
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-M : ℤ) := by
      have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      positivity
    filter_upwards [(hcoord i).eventually (eventually_le_nhds hpos)] with n hn
    exact (Padic.norm_int_le_pow_iff_dvd _ M).1 hn
  filter_upwards [hdvd] with n hn
  have hsum : y n = ∑ i, ((RingOfIntegers.basis K).repr (y n) i) • (RingOfIntegers.basis K) i :=
    ((RingOfIntegers.basis K).sum_repr (y n)).symm
  rw [hsum]
  refine Finset.dvd_sum fun i _ ↦ ?_
  obtain ⟨c, hc⟩ := hn i
  rw [hc, zsmul_eq_mul]
  exact Dvd.dvd.mul_right ⟨(c : 𝓞 K), by push_cast; ring⟩ _


end Implicit

section Explicit

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
Every global unit has a principal-unit power at every embedding into $\mathbb{C}_p$: with
$Q = |(\mathcal{O}_K/p)^\times|$ one has $\varepsilon^Q \equiv 1 \pmod{p}$
(`exists_pow_sub_one_dvd`), so $\|\sigma(\varepsilon)^Q - 1\| \le \|p\| < 1$.
-/
theorem hasPrincipalUnitPow_map (σ : K →+* ℂ_[p]) (u : (𝓞 K)ˣ) :
    PadicExpLog.HasPrincipalUnitPow (σ (u : K)) := by
  obtain ⟨Q, hQ0, hQ⟩ := exists_pow_sub_one_dvd (K := K) (p := p)
  obtain ⟨c, hc⟩ := hQ u
  refine ⟨Q, Nat.pos_of_ne_zero hQ0, ?_⟩
  have h1 : σ (u : K) ^ Q - 1 = ((p : ℕ) : ℂ_[p]) * σ (c : K) := by
    have := congrArg (fun x : 𝓞 K ↦ σ (x : K)) hc
    simpa only [map_sub, map_mul, map_pow, map_natCast, map_one, Units.val_pow_eq_pow_val,
      RingOfIntegers.coe_eq_algebraMap] using this
  rw [h1, norm_mul]
  calc ‖((p : ℕ) : ℂ_[p])‖ * ‖σ (c : K)‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ * 1 := by
        gcongr
        exact PadicExpLog.PadicComplex.norm_le_one_of_isIntegral
          ((RingOfIntegers.isIntegral_coe c).map_of_comp_eq (RingHom.id ℤ) σ (RingHom.ext_int _ _))
    _ < 1 := by
        rw [mul_one]
        exact PadicExpLog.PadicComplex.norm_natCast_p_lt_one

omit [NumberField K] in

/--
Converse to `eventually_pow_dvd_of_tendsto_map`: an algebraic integer divisible by a large power
of $p$ is small at every embedding into $\mathbb{C}_p$, since $\|\sigma(c)\| \leq 1$ for
$c \in \mathcal{O}_K$ (`PadicExpLog.PadicComplex.norm_le_one_of_isIntegral`).
-/
theorem tendsto_map_of_forall_eventually_dvd {y : ℕ → 𝓞 K}
    (hy : ∀ M : ℕ, ∀ᶠ n in atTop, (p : 𝓞 K) ^ M ∣ y n) (σ : K →+* ℂ_[p]) :
    Tendsto (fun n ↦ σ (y n : K)) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε
    (PadicExpLog.PadicComplex.norm_natCast_p_lt_one (p := p))
  filter_upwards [hy M] with n hn
  obtain ⟨c, hc⟩ := hn
  have hσ : σ (y n : K) = ((p : ℕ) : ℂ_[p]) ^ M * σ (c : K) := by
    have := congrArg (fun x : 𝓞 K ↦ σ (x : K)) hc
    simpa only [map_mul, map_pow, map_natCast, RingOfIntegers.coe_eq_algebraMap] using this
  rw [hσ, norm_mul, norm_pow]
  calc ‖((p : ℕ) : ℂ_[p])‖ ^ M * ‖σ (c : K)‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ M * 1 := by
        gcongr
        exact PadicExpLog.PadicComplex.norm_le_one_of_isIntegral
          ((RingOfIntegers.isIntegral_coe c).map_of_comp_eq (RingHom.id ℤ) σ (RingHom.ext_int _ _))
    _ < ε := by rwa [mul_one]

/--
The conjugate vector of any element of $K$ lies in the $\mathbb{Q}_p$-span of the conjugate
vectors of an integral basis. This span is the copy of $K \otimes_\mathbb{Q} \mathbb{Q}_p$
inside $\mathbb{C}_p^{[K:\mathbb{Q}]}$.
-/
theorem map_mem_span_integralBasis (x : K) :
    (fun σ : K →+* ℂ_[p] ↦ σ x) ∈ Submodule.span ℚ_[p]
      (Set.range fun k ↦ fun σ : K →+* ℂ_[p] ↦ σ (integralBasis K k)) := by
  classical
  have hx : (fun σ : K →+* ℂ_[p] ↦ σ x)
      = ∑ k, (algebraMap ℚ ℚ_[p] ((integralBasis K).repr x k)) •
          (fun σ : K →+* ℂ_[p] ↦ σ (integralBasis K k)) := by
    funext σ
    have hxs : x = ∑ k, ((integralBasis K).repr x k) • integralBasis K k :=
      ((integralBasis K).sum_repr x).symm
    conv_lhs => rw [hxs]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Rat.smul_def, map_mul, map_ratCast, Pi.smul_apply, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply, eq_ratCast]
  rw [hx]
  exact Submodule.sum_mem _ fun k _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Explicit

end Leopoldt
