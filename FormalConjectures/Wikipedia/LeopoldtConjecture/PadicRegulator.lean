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

import FormalConjecturesUtil
import FormalConjectures.Wikipedia.LeopoldtConjecture
import FormalConjectures.Wikipedia.LeopoldtConjecture.Elementary

/-!
# The `p`-adic-regulator form and the elementary form agree

`Leopoldt.leopoldt_conjecture.variants.padicRegulator` says the matrix of Iwasawa logarithms
`Leopoldt.logMatrix` has full rank $r_1 + r_2 - 1$. This file proves that equivalent to the
elementary form (`leopoldtConjecture_iff_rank`) and to the `p`-adic-relation form
(`forall_isPadicRelation_iff_rank`).

One direction takes logarithms of a relation $\prod_i \varepsilon_i^{a_i} = 1$; the other
descends a $\mathbb{C}_p$-linear relation among the rows of the log matrix to a nonzero
$\mathbb{Z}_p$-relation among the units, using that the rows lie in the $\mathbb{Q}_p$-span of
the conjugates of an integral basis.
-/

open Filter IsDedekindDomain NumberField NumberField.Units

open scoped NumberField

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
The Iwasawa logarithm turns a product of integer powers of units into a linear combination:
$\log_p \sigma(\prod_i \varepsilon_i^{n_i}) = \sum_i n_i \log_p \sigma(\varepsilon_i)$.

This uses that the Iwasawa logarithm is defined on all of $\mathbb{C}_p^\times$ and additive
there (`PadicExpLog.PadicComplex.hasIwasawaLog`, `PadicExpLog.iwasawaLog_prod`).
-/
@[category API, AMS 11]
theorem iwasawaLog_map_prod_zpow (σ : K →+* ℂ_[p]) (ε : Fin (rank K) → (𝓞 K)ˣ)
    (n : Fin (rank K) → ℤ) :
    PadicExpLog.iwasawaLog p (σ ((∏ i, ε i ^ n i : (𝓞 K)ˣ) : K)) =
      ∑ i, (n i : ℂ_[p]) * PadicExpLog.iwasawaLog p (σ (ε i : K)) := by
  have hne : ∀ i, σ (ε i : K) ≠ 0 := fun i ↦ (map_ne_zero σ).2 (coe_ne_zero _)
  have hσ : σ ((∏ i, ε i ^ n i : (𝓞 K)ˣ) : K) = ∏ i, σ (ε i : K) ^ n i := by
    have hcoe : ((∏ i, ε i ^ n i : (𝓞 K)ˣ) : K) = ∏ i, ((ε i : K) ^ n i) := by
      push_cast
      exact Finset.prod_congr rfl fun i _ ↦ coe_units_zpow (ε i) (n i)
    rw [hcoe, map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ map_zpow₀ σ _ _
  rw [hσ, PadicExpLog.iwasawaLog_prod PadicExpLog.PadicComplex.norm_natCast_p_lt_one
    fun i _ ↦ (PadicExpLog.PadicComplex.hasIwasawaLog (hne i)).zpow (n i)]
  exact Finset.sum_congr rfl fun i _ ↦
    PadicExpLog.iwasawaLog_zpow PadicExpLog.PadicComplex.norm_natCast_p_lt_one
      (PadicExpLog.PadicComplex.hasIwasawaLog (hne i)) (n i)

/--
**Taking logarithms in a $p$-adic relation.** If $\prod_i \varepsilon_i^{a_i} = 1$ in every
completion $K_\mathfrak{p}$ with $\mathfrak{p} \mid p$ (`IsPadicRelation`), then
$\sum_i a_i \log_p \sigma(\varepsilon_i) = 0$ for every embedding
$\sigma : K \to \mathbb{C}_p$.

This is the first half of [Nelson, Proposition 4.1]: the relation gives congruences
$\prod_i \varepsilon_i^{c_{i,n}} \equiv 1 \pmod{p^M}$ for the integer approximants
$c_{i,n}$ of $a_i$ (`eventually_dvd_of_tendsto`), hence
$\sigma(\prod_i \varepsilon_i^{c_{i,n}}) \to 1$ (`tendsto_map_of_forall_eventually_dvd`),
hence $\sum_i c_{i,n} \log_p \sigma(\varepsilon_i) \to 0$ by continuity of the logarithm at
$1$ (`PadicExpLog.tendsto_iwasawaLog_of_tendsto_one`); and $c_{i,n} \to a_i$ in
$\mathbb{C}_p$ (`tendsto_appr_cast`).
-/
@[category API, AMS 11]
theorem sum_iwasawaLog_eq_zero_of_isPadicRelation {ε : Fin (rank K) → (𝓞 K)ˣ}
    {a : Fin (rank K) → ℤ_[p]} (ha : IsPadicRelation K p ε a) (σ : K →+* ℂ_[p]) :
    ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * PadicExpLog.iwasawaLog p (σ (ε i : K)) = 0 := by
  set x : ℕ → (𝓞 K)ˣ := fun n ↦ ∏ i, ε i ^ (a i).appr n with hx
  -- The approximants are congruent to `1` modulo every power of `p`.
  have hdvd : ∀ M : ℕ, ∀ᶠ n in atTop, (p : 𝓞 K) ^ M ∣ ((x n : 𝓞 K) - 1) := fun M ↦
    eventually_dvd_of_tendsto (f := fun n ↦ (x n : 𝓞 K))
      (fun v hv ↦ (ha v hv).congr fun n ↦ by rw [coe_prod_pow]) M
  -- Hence they tend to `1` at every embedding, and their logarithms tend to `0`.
  have hone : Tendsto (fun n ↦ σ ((x n : 𝓞 K) : K)) atTop (nhds 1) := by
    have h0 := tendsto_map_of_forall_eventually_dvd K p (y := fun n ↦ (x n : 𝓞 K) - 1) hdvd σ
    have hfun : (fun n ↦ σ (((x n : 𝓞 K) - 1 : 𝓞 K) : K))
        = fun n ↦ σ ((x n : 𝓞 K) : K) - 1 := by
      funext n
      push_cast
      rw [map_sub, map_one]
    rw [hfun] at h0
    simpa using h0.add_const 1
  have hlog : Tendsto (fun n ↦ PadicExpLog.iwasawaLog p (σ ((x n : 𝓞 K) : K))) atTop (nhds 0) :=
    PadicExpLog.tendsto_iwasawaLog_of_tendsto_one
      PadicExpLog.PadicComplex.norm_natCast_p_lt_one hone
  -- The logarithm of the approximant is the approximating sum.
  have heq : ∀ n, PadicExpLog.iwasawaLog p (σ ((x n : 𝓞 K) : K))
      = ∑ i, (((a i).appr n : ℕ) : ℂ_[p]) * PadicExpLog.iwasawaLog p (σ (ε i : K)) := by
    intro n
    have hz : x n = ∏ i, ε i ^ (((a i).appr n : ℕ) : ℤ) := by
      rw [hx]
      exact Finset.prod_congr rfl fun i _ ↦ (zpow_natCast _ _).symm
    rw [hz, iwasawaLog_map_prod_zpow K p σ ε]
    exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring
  -- Pass to the limit in each summand.
  have hsum : Tendsto (fun n ↦ ∑ i, (((a i).appr n : ℕ) : ℂ_[p]) *
      PadicExpLog.iwasawaLog p (σ (ε i : K))) atTop
      (nhds (∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) *
        PadicExpLog.iwasawaLog p (σ (ε i : K)))) :=
    tendsto_finsetSum _ fun i _ ↦ (tendsto_appr_cast p (a i)).mul_const _
  refine tendsto_nhds_unique hsum ?_
  simpa only [heq] using hlog

/--
If $\varepsilon_i^N = \prod_j \varepsilon_j^{C_{ij}}$ expresses the $N$-th powers of a family
of units in terms of the fundamental system, then
$N \log_p \sigma(\varepsilon_i) = \sum_j C_{ij} \log_p \sigma(\varepsilon_j)$, i.e. the
logarithm vector of $\varepsilon_i$ is the $C$-combination of the rows of `logMatrix`.
-/
@[category API, AMS 11]
theorem mul_iwasawaLog_map_eq_sum_logMatrix (σ : K →+* ℂ_[p]) (ε : Fin (rank K) → (𝓞 K)ˣ)
    (C : Matrix (Fin (rank K)) (Fin (rank K)) ℤ) (N : ℕ)
    (hC : ∀ i, ε i ^ N = ∏ j, fundSystem K j ^ C i j) (i : Fin (rank K)) :
    (N : ℂ_[p]) * PadicExpLog.iwasawaLog p (σ (ε i : K)) =
      ∑ j, (C i j : ℂ_[p]) * logMatrix K p j σ := by
  have hpow : PadicExpLog.iwasawaLog p (σ ((ε i ^ N : (𝓞 K)ˣ) : K))
      = (N : ℂ_[p]) * PadicExpLog.iwasawaLog p (σ (ε i : K)) := by
    rw [show ((ε i ^ N : (𝓞 K)ˣ) : K) = ((ε i : K)) ^ N by push_cast; ring, map_pow,
      PadicExpLog.iwasawaLog_pow PadicExpLog.PadicComplex.norm_natCast_p_lt_one
        (PadicExpLog.PadicComplex.hasIwasawaLog ((map_ne_zero σ).2 (coe_ne_zero _)))]
  rw [← hpow, hC i, iwasawaLog_map_prod_zpow K p σ (fundSystem K) (C i)]
  rfl

/--
**Full rank of the logarithm matrix implies Leopoldt's conjecture** (the first half of
[Nelson, Proposition 4.1]). If the rows of `logMatrix K p` are `ℂ_p`-linearly independent, then
the only $p$-adic relation among a family of units of maximal rank is the trivial one.

Taking logarithms turns the relation into $\sum_i a_i \log_p \sigma(\varepsilon_i) = 0$
(`sum_iwasawaLog_eq_zero_of_isPadicRelation`); writing
$\varepsilon_i^N = \prod_j \varepsilon_j^{C_{ij}}$ makes this a relation among the rows of
`logMatrix` (`mul_iwasawaLog_map_eq_sum_logMatrix`), so $aC = 0$, and $\det C \neq 0$
(`det_ne_zero_of_isMaxRank`) forces $a = 0$.
-/
@[category API, AMS 11]
theorem eq_zero_of_isPadicRelation_of_rank (h : (logMatrix K p).rank = rank K)
    {ε : Fin (rank K) → (𝓞 K)ˣ} (hmax : IsMaxRank ε) {a : Fin (rank K) → ℤ_[p]}
    (ha : IsPadicRelation K p ε a) : a = 0 := by
  classical
  have hw : torsionOrder K ≠ 0 := torsionOrder_ne_zero K
  choose ζe hζe using fun i ↦ (exist_unique_eq_mul_prod K (ε i)).exists
  set C : Matrix (Fin (rank K)) (Fin (rank K)) ℤ := fun i j ↦ (ζe i).2 j * torsionOrder K
  have hC : ∀ i, ε i ^ torsionOrder K = ∏ j, fundSystem K j ^ C i j := by
    intro i
    have hζ : ((ζe i).1 : (𝓞 K)ˣ) ^ torsionOrder K = 1 :=
      (mem_rootsOfUnity _ _).1 (by rw [rootsOfUnity_eq_torsion]; exact (ζe i).1.2)
    rw [hζe i, mul_pow, hζ, one_mul, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← zpow_natCast, ← zpow_mul]
  have hdet : C.det ≠ 0 := det_ne_zero_of_isMaxRank (isMaxRank_pow hmax hw) C hC
  -- The rows of the logarithm matrix are linearly independent.
  have hli : LinearIndependent ℂ_[p] (logMatrix K p).row :=
    (Matrix.rank_eq_card_iff_linearIndependent_row _).1 (by rw [h, Fintype.card_fin])
  -- The coefficient vector `a C` annihilates every row.
  set b : Fin (rank K) → ℂ_[p] :=
    fun j ↦ ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * (C i j : ℂ_[p]) with hb
  have hzero : ∀ j, b j = 0 := by
    refine Fintype.linearIndependent_iff.1 hli b (funext fun σ ↦ ?_)
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hlog := sum_iwasawaLog_eq_zero_of_isPadicRelation K p ha σ
    have hrow : ∑ j, b j * (logMatrix K p).row j σ
        = ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) *
            ((torsionOrder K : ℂ_[p]) * PadicExpLog.iwasawaLog p (σ (ε i : K))) := by
      simp only [hb, Finset.sum_mul, Matrix.row]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_iwasawaLog_map_eq_sum_logMatrix K p σ ε C (torsionOrder K) hC i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hfactor : ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) *
        ((torsionOrder K : ℂ_[p]) * PadicExpLog.iwasawaLog p (σ (ε i : K)))
        = (torsionOrder K : ℂ_[p]) * ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) *
            PadicExpLog.iwasawaLog p (σ (ε i : K)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hrow, hfactor, hlog, mul_zero]
  -- Descend the relation to `ℤ_[p]` and invert `C` by its adjugate.
  have hvec : Matrix.vecMul a ((Int.castRingHom ℤ_[p]).mapMatrix C) = 0 := by
    funext j
    have hj : algebraMap ℚ_[p] ℂ_[p]
        ((Matrix.vecMul a ((Int.castRingHom ℤ_[p]).mapMatrix C) j : ℤ_[p]) : ℚ_[p]) = 0 := by
      rw [← hzero j, hb]
      simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
        eq_intCast]
      rw [PadicInt.coe_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [PadicInt.coe_mul, map_mul, PadicInt.coe_intCast, map_intCast]
    have h1 : ((Matrix.vecMul a ((Int.castRingHom ℤ_[p]).mapMatrix C) j : ℤ_[p]) : ℚ_[p]) = 0 :=
      (map_eq_zero_iff _ (algebraMap ℚ_[p] ℂ_[p]).injective).1 hj
    exact Subtype.ext h1
  have hdet' : ((Int.castRingHom ℤ_[p]).mapMatrix C).det ≠ 0 := by
    rw [← RingHom.map_det, eq_intCast, Int.cast_ne_zero]
    exact hdet
  have := congrArg (fun x ↦ Matrix.vecMul x ((Int.castRingHom ℤ_[p]).mapMatrix C).adjugate) hvec
  simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
    Matrix.zero_vecMul] at this
  exact (smul_eq_zero.1 this).resolve_left hdet'

/--
**The rows of the logarithm matrix are defined over $\mathbb{Q}_p$**: each row lies in the
$\mathbb{Q}_p$-span of the conjugate vectors of an integral basis.

This is what replaces the Galois-trace descent of [Nelson, (4.4)] for a general number field.
The row is the limit of the vectors
$\sigma \mapsto (\sigma(\varepsilon_i^{Q p^k}) - 1) / (Q p^k)$
(`PadicExpLog.tendsto_padicLog`), each of which lies in the span
(`map_mem_span_integralBasis`), and the span is closed because it is finite-dimensional over the
complete field $\mathbb{Q}_p$ (`Submodule.closed_of_finiteDimensional`).
-/
@[category API, AMS 11]
theorem logMatrix_mem_span (i : Fin (rank K)) :
    logMatrix K p i ∈ Submodule.span ℚ_[p]
      (Set.range fun k ↦ fun σ : K →+* ℂ_[p] ↦ σ (integralBasis K k)) := by
  classical
  set V := Submodule.span ℚ_[p]
    (Set.range fun k ↦ fun σ : K →+* ℂ_[p] ↦ σ (integralBasis K k)) with hV
  have hfin : FiniteDimensional ℚ_[p] V :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hclosed : IsClosed (V : Set ((K →+* ℂ_[p]) → ℂ_[p])) :=
    Submodule.closed_of_finiteDimensional _
  obtain ⟨Q, hQ0, hQ⟩ := exists_pow_sub_one_dvd (K := K) (p := p)
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
  have hunit : ∀ σ : K →+* ℂ_[p], ‖σ (fundSystem K i : K) ^ Q - 1‖ < 1 := by
    intro σ
    obtain ⟨Q', hQ'pos, hQ'⟩ := hasPrincipalUnitPow_map K p σ (fundSystem K i)
    obtain ⟨c, hc⟩ := hQ (fundSystem K i)
    have h1 : σ (fundSystem K i : K) ^ Q - 1 = ((p : ℕ) : ℂ_[p]) * σ (c : K) := by
      have := congrArg (fun x : 𝓞 K ↦ σ (x : K)) hc
      simpa only [map_sub, map_mul, map_pow, map_natCast, map_one, Units.val_pow_eq_pow_val,
        RingOfIntegers.coe_eq_algebraMap] using this
    rw [h1, norm_mul]
    calc ‖((p : ℕ) : ℂ_[p])‖ * ‖σ (c : K)‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ * 1 := by
          gcongr
          exact PadicExpLog.PadicComplex.norm_le_one_of_isIntegral
            ((RingOfIntegers.isIntegral_coe c).map_of_comp_eq (RingHom.id ℤ) σ
              (RingHom.ext_int _ _))
      _ < 1 := by
          rw [mul_one]
          exact PadicExpLog.PadicComplex.norm_natCast_p_lt_one
  -- The approximating vectors lie in `V`.
  have hterm : ∀ k : ℕ, (fun σ : K →+* ℂ_[p] ↦
      ((σ (fundSystem K i : K) ^ Q) ^ p ^ k - 1) / ((p : ℕ) : ℂ_[p]) ^ k / (Q : ℂ_[p])) ∈ V := by
    intro k
    have hx : (fun σ : K →+* ℂ_[p] ↦
        ((σ (fundSystem K i : K) ^ Q) ^ p ^ k - 1) / ((p : ℕ) : ℂ_[p]) ^ k / (Q : ℂ_[p]))
        = (algebraMap ℚ_[p] ℚ_[p] (((p : ℚ_[p]) ^ k * (Q : ℚ_[p]))⁻¹)) •
          (fun σ : K →+* ℂ_[p] ↦ σ (((fundSystem K i : K) ^ (Q * p ^ k) - 1))) := by
      funext σ
      rw [Pi.smul_apply, Algebra.smul_def, map_sub, map_pow, map_one, pow_mul]
      simp only [map_inv₀, map_mul, map_pow, map_natCast]
      field_simp
    rw [hx]
    exact Submodule.smul_mem _ _ (map_mem_span_integralBasis K p _)
  -- The row is the limit of those vectors.
  have hlim : Tendsto (fun k : ℕ ↦ (fun σ : K →+* ℂ_[p] ↦
      ((σ (fundSystem K i : K) ^ Q) ^ p ^ k - 1) / ((p : ℕ) : ℂ_[p]) ^ k / (Q : ℂ_[p])))
      atTop (nhds (logMatrix K p i)) := by
    refine tendsto_pi_nhds.2 fun σ ↦ ?_
    rw [logMatrix_apply_eq_div K p i σ hQpos (hunit σ)]
    exact (PadicExpLog.tendsto_padicLog PadicExpLog.PadicComplex.norm_natCast_p_lt_one
      (hunit σ)).div_const _
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hterm)

/--
**A `ℂ_p`-relation among the rows of the logarithm matrix descends to a nonzero `ℤ_p`-relation**
(the descent step of [Nelson, Proposition 4.1]).

The rows lie in the `ℚ_p`-span of the conjugate vectors of an integral basis
(`logMatrix_mem_span`), and those vectors are `ℂ_p`-linearly independent
(`NumberField.linearIndependent_embeddings_of_basis`), so a `ℂ_p`-relation among the rows is a
`ℂ_p`-relation among their `ℚ_p`-coordinate vectors, hence a `ℚ_p`-relation
(`linearIndependent_algebraMap_comp_iff`). Clearing denominators
(`IsLocalization.exist_integer_multiples`) makes the coefficients `p`-adic integers. This
replaces the decomposition-group trace of [Nelson, (4.4)], which needs `K/ℚ` Galois.
-/
@[category API, AMS 11]
theorem exists_ne_zero_sum_logMatrix_eq_zero
    (h : ¬ LinearIndependent ℂ_[p] (logMatrix K p).row) :
    ∃ a : Fin (rank K) → ℤ_[p], a ≠ 0 ∧
      ∀ σ : K →+* ℂ_[p], ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * logMatrix K p i σ = 0 := by
  classical
  set w : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ((K →+* ℂ_[p]) → ℂ_[p]) :=
    fun k ↦ fun σ ↦ σ (integralBasis K k) with hw
  have hwli : LinearIndependent ℂ_[p] w :=
    NumberField.linearIndependent_embeddings_of_basis (E := ℂ_[p]) (integralBasis K)
  choose B hB using fun i ↦ (Submodule.mem_span_range_iff_exists_fun ℚ_[p]).1
    (logMatrix_mem_span K p i)
  have hBσ : ∀ (i : Fin (rank K)) (σ : K →+* ℂ_[p]),
      logMatrix K p i σ = ∑ k, algebraMap ℚ_[p] ℂ_[p] (B i k) * w k σ := by
    intro i σ
    rw [← hB i, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [Pi.smul_apply, Algebra.smul_def]
  have hdepB : ¬ LinearIndependent ℂ_[p] (fun i ↦ algebraMap ℚ_[p] ℂ_[p] ∘ B i) := by
    rw [Fintype.linearIndependent_iff] at h ⊢
    push Not at h ⊢
    obtain ⟨c, hc, i₀, hi₀⟩ := h
    refine ⟨c, funext fun k ↦ ?_, i₀, hi₀⟩
    have hzero : ∑ k, (∑ i, c i * algebraMap ℚ_[p] ℂ_[p] (B i k)) • w k = 0 := by
      funext σ
      rw [Finset.sum_apply, Pi.zero_apply]
      have hcσ : ∑ i, c i * logMatrix K p i σ = 0 := by
        have hcc := congrFun hc σ
        simpa [Finset.sum_apply, Matrix.row] using hcc
      rw [← hcσ]
      simp only [Pi.smul_apply, smul_eq_mul, hBσ, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact (Finset.sum_comm).symm
    have hk := Fintype.linearIndependent_iff.1 hwli _ hzero k
    simpa using hk
  rw [linearIndependent_algebraMap_comp_iff, Fintype.linearIndependent_iff] at hdepB
  push Not at hdepB
  obtain ⟨d, hd, j₀, hj₀⟩ := hdepB
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ_[p])
    Finset.univ d
  choose a ha using fun i ↦ hm i (Finset.mem_univ i)
  have hm0 : (m : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero m
  refine ⟨a, ?_, fun σ ↦ ?_⟩
  · intro hzero
    apply hj₀
    have h1 := ha j₀
    rw [congrFun hzero j₀] at h1
    simp only [Algebra.smul_def] at h1
    rcases mul_eq_zero.1 h1.symm with h2 | h2
    · exact absurd ((map_eq_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).1 h2) hm0
    · exact h2
  · have hdk : ∀ k, ∑ i, d i * B i k = 0 := fun k ↦ by
      have hdd := congrFun hd k
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hdd
    have hrel : ∑ i, algebraMap ℚ_[p] ℂ_[p] (d i) * logMatrix K p i σ = 0 := by
      have hexp : ∑ i, algebraMap ℚ_[p] ℂ_[p] (d i) * logMatrix K p i σ
          = ∑ k, algebraMap ℚ_[p] ℂ_[p] (∑ i, d i * B i k) * w k σ := by
        simp only [map_sum, map_mul, hBσ, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
      rw [hexp]
      simp [hdk]
    calc ∑ i, algebraMap ℚ_[p] ℂ_[p] ((a i : ℤ_[p]) : ℚ_[p]) * logMatrix K p i σ
        = algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (m : ℤ_[p])) *
            ∑ i, algebraMap ℚ_[p] ℂ_[p] (d i) * logMatrix K p i σ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [show ((a i : ℤ_[p]) : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (a i) from rfl, ha i,
            Algebra.smul_def, map_mul, mul_assoc]
      _ = 0 := by rw [hrel, mul_zero]

/--
**The approximants of a `ℤ_p`-relation tend to `1` at every embedding** (the `exp` step of
[Nelson, Proposition 4.1], replaced here by the isometry of the logarithm).

Choose `Q` with $p^2 \mid \varepsilon_i^Q - 1$, so that every $\sigma(\varepsilon_i^Q)$ lies in
the disc $\|u - 1\|^{p-1} < \|p\|$ where $\log_p$ is an isometry
(`PadicExpLog.norm_padicLog_eq'`, valid for every prime, `p = 2` included). For
$x_m = \prod_i \varepsilon_i^{Q c_{i,m}}$ with $c_{i,m}$ the approximants of $a_i$, the relation
gives $\log_p \sigma(x_m) = \sum_i (c_{i,m} - a_i) \log_p \sigma(\varepsilon_i^Q)$, of norm at
most $p^{-m}$ times a constant, so $\|\sigma(x_m) - 1\| \to 0$.
-/
@[category API, AMS 11]
theorem tendsto_map_prod_pow_appr {a : Fin (rank K) → ℤ_[p]}
    (hrel : ∀ σ : K →+* ℂ_[p],
      ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * logMatrix K p i σ = 0)
    {Q : ℕ}
    (hQ : ∀ i, (p : 𝓞 K) ^ 2 ∣ ((fundSystem K i ^ Q : (𝓞 K)ˣ) : 𝓞 K) - 1)
    (σ : K →+* ℂ_[p]) :
    Tendsto (fun m ↦ σ ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : K))
      atTop (nhds 1) := by
  classical
  have hppos : (0 : ℝ) < ‖((p : ℕ) : ℂ_[p])‖ := by
    have : ((p : ℕ) : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    exact norm_pos_iff.2 this
  have hplt : ‖((p : ℕ) : ℂ_[p])‖ < 1 := PadicExpLog.PadicComplex.norm_natCast_p_lt_one
  -- Each `σ (ε_i ^ Q)` is a `1`-unit, in fact within `‖p‖ ^ 2` of `1`.
  set η : Fin (rank K) → ℂ_[p] := fun i ↦ σ (fundSystem K i : K) ^ Q with hη
  have hηsub : ∀ i, ‖η i - 1‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ 2 := by
    intro i
    obtain ⟨c, hc⟩ := hQ i
    have h1 : η i - 1 = ((p : ℕ) : ℂ_[p]) ^ 2 * σ (c : K) := by
      have := congrArg (fun x : 𝓞 K ↦ σ (x : K)) hc
      simpa only [hη, map_sub, map_mul, map_pow, map_natCast, map_one, Units.val_pow_eq_pow_val,
        RingOfIntegers.coe_eq_algebraMap] using this
    rw [h1, norm_mul, norm_pow]
    refine mul_le_of_le_one_right (by positivity) ?_
    exact PadicExpLog.PadicComplex.norm_le_one_of_isIntegral
      ((RingOfIntegers.isIntegral_coe c).map_of_comp_eq (RingHom.id ℤ) σ (RingHom.ext_int _ _))
  have hdisc : ∀ i, ‖η i - 1‖ ^ (p - 1) < ‖((p : ℕ) : ℂ_[p])‖ := by
    intro i
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    calc ‖η i - 1‖ ^ (p - 1) ≤ (‖((p : ℕ) : ℂ_[p])‖ ^ 2) ^ (p - 1) := by
          gcongr
          exact hηsub i
      _ ≤ (‖((p : ℕ) : ℂ_[p])‖ ^ 2) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by nlinarith) (by omega)
      _ < ‖((p : ℕ) : ℂ_[p])‖ := by
          rw [pow_one, sq]
          exact mul_lt_of_lt_one_left hppos hplt
  have hηne : ∀ i, η i ≠ 0 := fun i ↦
    pow_ne_zero _ ((map_ne_zero σ).2 (coe_ne_zero _))
  have hηnorm : ∀ i, ‖η i‖ ≤ 1 := fun i ↦
    le_of_eq (PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one
      ((hηsub i).trans_lt (by nlinarith)))
  -- The approximants.
  set x : ℕ → ℂ_[p] := fun m ↦ ∏ i, η i ^ (a i).appr m with hx
  have hxeq : ∀ m, σ ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : K) = x m := by
    intro m
    rw [hx]
    push_cast
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by simp only [hη, map_pow, pow_mul]
  have hxsub : ∀ m, ‖x m - 1‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ 2 := by
    intro m
    simp only [hx]
    refine PadicExpLog.norm_prod_sub_one_le (by positivity) (fun i _ ↦ ?_) (fun i _ ↦ ?_)
    · rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hηnorm i)
    · exact (PadicExpLog.norm_pow_sub_one_le (hηnorm i) _).trans (hηsub i)
  have hxdisc : ∀ m, ‖x m - 1‖ ^ (p - 1) < ‖((p : ℕ) : ℂ_[p])‖ := by
    intro m
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    calc ‖x m - 1‖ ^ (p - 1) ≤ (‖((p : ℕ) : ℂ_[p])‖ ^ 2) ^ (p - 1) := by
          gcongr
          exact hxsub m
      _ ≤ (‖((p : ℕ) : ℂ_[p])‖ ^ 2) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by nlinarith) (by omega)
      _ < ‖((p : ℕ) : ℂ_[p])‖ := by
          rw [pow_one, sq]
          exact mul_lt_of_lt_one_left hppos hplt
  -- The logarithm of the approximant, rewritten through the relation.
  have hηlog : ∀ i, PadicExpLog.iwasawaLog p (η i) = (Q : ℂ_[p]) * logMatrix K p i σ := by
    intro i
    rw [hη, PadicExpLog.iwasawaLog_pow PadicExpLog.PadicComplex.norm_natCast_p_lt_one
      (PadicExpLog.PadicComplex.hasIwasawaLog ((map_ne_zero σ).2 (coe_ne_zero _)))]
    rfl
  have hlogx : ∀ m, PadicExpLog.iwasawaLog p (x m)
      = ∑ i, ((((a i).appr m : ℕ) : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p])) *
          ((Q : ℂ_[p]) * logMatrix K p i σ) := by
    intro m
    have hprod : PadicExpLog.iwasawaLog p (x m)
        = ∑ i, (((a i).appr m : ℕ) : ℂ_[p]) * ((Q : ℂ_[p]) * logMatrix K p i σ) := by
      simp only [hx]
      rw [PadicExpLog.iwasawaLog_prod (f := fun i ↦ η i ^ (a i).appr m)
        PadicExpLog.PadicComplex.norm_natCast_p_lt_one
        fun i _ ↦ (PadicExpLog.PadicComplex.hasIwasawaLog (hηne i)).pow _]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [PadicExpLog.iwasawaLog_pow PadicExpLog.PadicComplex.norm_natCast_p_lt_one
        (PadicExpLog.PadicComplex.hasIwasawaLog (hηne i)), hηlog i]
    rw [hprod]
    have hzero : ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * ((Q : ℂ_[p]) * logMatrix K p i σ)
        = 0 := by
      have := hrel σ
      calc ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * ((Q : ℂ_[p]) * logMatrix K p i σ)
          = (Q : ℂ_[p]) * ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * logMatrix K p i σ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ by ring
        _ = 0 := by rw [this, mul_zero]
    rw [← sub_zero (∑ i, (((a i).appr m : ℕ) : ℂ_[p]) * ((Q : ℂ_[p]) * logMatrix K p i σ)),
      ← hzero, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- Bound the logarithm, hence the distance to `1`, by `p ^ (-m)` times a constant.
  set C : ℝ := ∑ i, ‖(Q : ℂ_[p]) * logMatrix K p i σ‖ with hC
  have hbound : ∀ m, ‖x m - 1‖ ≤ ((p : ℝ)⁻¹) ^ m * C := by
    intro m
    rw [← PadicExpLog.norm_padicLog_eq' PadicExpLog.PadicComplex.norm_natCast_p_lt_one (hxdisc m),
      ← PadicExpLog.iwasawaLog_of_norm_sub_one_lt PadicExpLog.PadicComplex.norm_natCast_p_lt_one
        (PadicExpLog.norm_sub_one_lt_one_of_pow_lt
          PadicExpLog.PadicComplex.norm_natCast_p_lt_one (hxdisc m)),
      hlogx m, hC, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_appr_sub_le p (a i) m) (norm_nonneg _)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlim : Tendsto (fun m : ℕ ↦ ((p : ℝ)⁻¹) ^ m * C) atTop (nhds 0) := by
    have hinv : ((p : ℝ)⁻¹) < 1 := by
      rw [inv_lt_one₀] <;> linarith
    have h0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hinv).mul_const C
  simp only [hxeq]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun m ↦ norm_nonneg _) hbound hlim

/--
**A nonzero `ℤ_p`-relation whose approximants are congruent to `1` refutes the elementary form of
Leopoldt's conjecture.** If $a \neq 0$ and $p^M$ divides
$\prod_i \varepsilon_i^{Q c_{i,m}} - 1$ for every $M$ and all large $m$, then the exponents
$Q c_{i_0,m}$ have $p$-adic absolute value bounded below by
$\|Q\| \cdot \|a_{i_0}\| > 0$, uniformly in $m$, so they are not divisible by an arbitrarily
large power of $p$, which is what the conjecture asserts.
-/
@[category API, AMS 11]
theorem not_leopoldtConjecture_of_forall_eventually_dvd {a : Fin (rank K) → ℤ_[p]} (ha : a ≠ 0)
    {Q : ℕ} (hQ : Q ≠ 0)
    (h : ∀ M : ℕ, ∀ᶠ m in atTop, (p : 𝓞 K) ^ M ∣
      ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : 𝓞 K) - 1) :
    ¬ LeopoldtConjecture K p := by
  classical
  intro hL
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (funext hcon)
  have hppos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := by rw [inv_lt_one₀] <;> linarith
  have hQne : ((Q : ℕ) : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hQ
  set t : ℝ := ‖((Q : ℕ) : ℤ_[p])‖ * ‖a i₀‖ with ht
  have htpos : 0 < t := mul_pos (norm_pos_iff.2 hQne) (norm_pos_iff.2 hi₀)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : ℝ)⁻¹) ^ N < t := exists_pow_lt_of_lt_one htpos hpinv
  have hNlt : (p : ℝ) ^ (-N : ℤ) < t := by rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨m₀, hm₀'⟩ : ∃ m₀ : ℕ, ((p : ℝ)⁻¹) ^ m₀ < ‖a i₀‖ :=
    exists_pow_lt_of_lt_one (norm_pos_iff.2 hi₀) hpinv
  have hm₀ : (p : ℝ) ^ (-m₀ : ℤ) < ‖a i₀‖ := by rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨M, hM⟩ := hL N
  obtain ⟨m, hmdvd, hmge⟩ := ((h M).and (eventually_ge_atTop m₀)).exists
  -- The exponent vector at stage `m` satisfies the congruence of `LeopoldtConjecture`.
  have hprod : (∏ i, fundSystem K i ^ ((Q * (a i).appr m : ℕ) : ℤ))
      = ∏ i, fundSystem K i ^ (Q * (a i).appr m) :=
    Finset.prod_congr rfl fun i _ ↦ zpow_natCast _ _
  have hexp : ((p : ℤ) ^ N) ∣ ((Q * (a i₀).appr m : ℕ) : ℤ) :=
    hM (fun i ↦ ((Q * (a i).appr m : ℕ) : ℤ)) (by rw [hprod]; exact hmdvd) i₀
  -- But the `p`-adic norm of that exponent is bounded below, uniformly in `m`.
  have hnormappr : ‖((a i₀).appr m : ℤ_[p])‖ = ‖a i₀‖ := by
    have hclose : ‖((a i₀).appr m : ℤ_[p]) - a i₀‖ < ‖a i₀‖ := by
      refine lt_of_le_of_lt ?_ hm₀
      rw [norm_sub_rev]
      refine le_trans ((PadicInt.norm_le_pow_iff_mem_span_pow _ m).2
        (PadicInt.appr_spec m (a i₀))) ?_
      exact zpow_le_zpow_right₀ hp1.le (by omega)
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (x := a i₀) (y := ((a i₀).appr m : ℤ_[p]) - a i₀) (by
        intro hcon
        exact absurd hcon.symm hclose.ne)
    rw [add_sub_cancel] at this
    rw [this, max_eq_left hclose.le]
  have hnormQ : ‖(((Q * (a i₀).appr m : ℕ) : ℤ) : ℤ_[p])‖ = t := by
    rw [ht, ← hnormappr]
    push_cast
    rw [norm_mul]
  have hle : ‖(((Q * (a i₀).appr m : ℕ) : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-N : ℤ) :=
    PadicInt.norm_int_le_pow_iff_dvd.2 (by exact_mod_cast hexp)
  rw [hnormQ] at hle
  exact absurd hle (not_le.2 hNlt)

/--
**Leopoldt's conjecture fails if the rows of the logarithm matrix satisfy a nonzero
`ℤ_p`-relation** (the second half of [Nelson, Proposition 4.1]).

Take $Q = Q_0 p$ with $\varepsilon_i^{Q_0} \equiv 1 \pmod p$ (`exists_pow_sub_one_dvd`), so that
$p^2 \mid \varepsilon_i^Q - 1$ (`pow_pow_sub_one_dvd`). Then the approximants of the relation
tend to $1$ at every embedding (`tendsto_map_prod_pow_appr`), hence are congruent to $1$ modulo
every power of $p$ (`eventually_pow_dvd_of_tendsto_map`), which contradicts the conjecture
(`not_leopoldtConjecture_of_forall_eventually_dvd`).
-/
@[category API, AMS 11]
theorem not_leopoldtConjecture_of_exists_relation {a : Fin (rank K) → ℤ_[p]} (ha : a ≠ 0)
    (hrel : ∀ σ : K →+* ℂ_[p],
      ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * logMatrix K p i σ = 0) :
    ¬ LeopoldtConjecture K p := by
  classical
  obtain ⟨Q₀, hQ₀, hQ₀'⟩ := exists_pow_sub_one_dvd (K := K) (p := p)
  set Q : ℕ := Q₀ * p with hQdef
  have hQ : Q ≠ 0 := mul_ne_zero hQ₀ (Fact.out : p.Prime).ne_zero
  have hQsq : ∀ i, (p : 𝓞 K) ^ 2 ∣ ((fundSystem K i ^ Q : (𝓞 K)ˣ) : 𝓞 K) - 1 := by
    intro i
    have hstep := pow_pow_sub_one_dvd (hQ₀' (fundSystem K i)) 1
    rw [pow_one] at hstep
    rw [hQdef, pow_mul]
    exact hstep
  refine not_leopoldtConjecture_of_forall_eventually_dvd K p ha hQ fun M ↦ ?_
  refine eventually_pow_dvd_of_tendsto_map
    (y := fun m ↦ ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : 𝓞 K) - 1)
    (fun σ ↦ ?_) M
  have h0 := tendsto_map_prod_pow_appr K p hrel hQsq σ
  have hfun : (fun m ↦ σ ((((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : 𝓞 K) - 1 : 𝓞 K) : K))
      = fun m ↦ σ ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : K) - 1 := by
    funext m
    push_cast
    rw [map_sub, map_one]
  rw [hfun]
  simpa using h0.sub_const 1

/--
**The equivalence of the two forms of Leopoldt's conjecture** [Nelson, Proposition 4.1]: the
elementary congruence form `LeopoldtConjecture` holds if and only if the matrix of $p$-adic
logarithms of a fundamental system of units has full rank $r_1 + r_2 - 1$.

The forward direction is by contraposition: if the rank is not full, the rows are
`ℂ_p`-dependent (`Matrix.rank_eq_card_iff_linearIndependent_row`), that dependence descends to a
nonzero `ℤ_p`-relation (`exists_ne_zero_sum_logMatrix_eq_zero`), and such a relation contradicts
the conjecture (`not_leopoldtConjecture_of_exists_relation`). The converse is
`eq_zero_of_isPadicRelation_of_rank` fed into `leopoldtConjecture_of_forall_isPadicRelation`.
-/
@[category API, AMS 11]
theorem leopoldtConjecture_iff_rank :
    LeopoldtConjecture K p ↔ (logMatrix K p).rank = rank K := by
  refine ⟨fun h ↦ ?_, fun h ↦ leopoldtConjecture_of_forall_isPadicRelation
    fun ε hmax _ a ha ↦ eq_zero_of_isPadicRelation_of_rank K p h hmax ha⟩
  by_contra hrank
  have hli : ¬ LinearIndependent ℂ_[p] (logMatrix K p).row := fun hli ↦
    hrank (by simpa using (Matrix.rank_eq_card_iff_linearIndependent_row _).2 hli)
  obtain ⟨a, hane, hrel⟩ := exists_ne_zero_sum_logMatrix_eq_zero K p hli
  exact not_leopoldtConjecture_of_exists_relation K p hane hrel h

/--
The hypotheses of `leopoldt_conjecture` (the `IsPadicRelation` form) are equivalent to
`leopoldt_conjecture.variants.padicRegulator` (the rank form).
-/
@[category API, AMS 11]
theorem forall_isPadicRelation_iff_rank :
    (∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
        ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0) ↔
      (logMatrix K p).rank = rank K :=
  (leopoldtConjecture_iff K p).symm.trans (leopoldtConjecture_iff_rank K p)

/-
### The `p`-adic regulator of a totally real field

For totally real `K` the matrix `logMatrix K p` has `r + 1` columns and its rows sum to zero, so
deleting any one column gives an `r × r` matrix whose determinant is well defined up to sign:
Washington's `p`-adic regulator `R_p(K)`.
-/

end Leopoldt
