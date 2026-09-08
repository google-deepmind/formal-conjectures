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

/-!
# The $\mathbb{Z}_p$-rank form and the `p`-adic-relation form agree

`Leopoldt.leopoldt_conjecture.variants.zpRank` is Wikipedia's statement: the
$\mathbb{Z}_p$-rank of the closure `Leopoldt.closureE₁` of $E_1$ in $U_1$ is $r_1 + r_2 - 1$.
This file proves it equivalent to `Leopoldt.leopoldt_conjecture` (`zpRank_iff`).

Fix units of maximal rank lying in $E_1$. They span a $\mathbb{Z}_p$-linear map
$\varphi_\varepsilon : \mathbb{Z}_p^r \to U_1$ (`unitsLinearMap`) whose kernel is exactly the
$p$-adic relations (`isPadicRelation_iff`) and whose image has finite index in the closure
(`index_smul_mem_range`). Rank-nullity then turns injectivity into the rank statement.
-/

open Filter IsDedekindDomain NumberField NumberField.Units Topology

open scoped NumberField Valued

namespace Leopoldt

section equivalence

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable (ε : Fin (rank K) → (𝓞 K)ˣ) (hone : ∀ i, IsPrincipalUnitAbove K p (ε i))

/-- The units $\varepsilon_i$ as elements of $E_1$. -/
def toE₁ (i : Fin (rank K)) : Additive (E₁ K p) := Additive.ofMul ⟨ε i, hone i⟩

/-- The $\mathbb{Z}_p$-linear map $\varphi_\varepsilon : \mathbb{Z}_p^r \to U_1$,
$a \mapsto \sum_i a_i \cdot \varepsilon_i$, i.e. $\prod_i \varepsilon_i^{a_i}$ multiplicatively.
This is the map $\lambda_{K,p}$ of [Ferri–Johnston, §1] restricted to
$\mathbb{Z}_p \otimes \langle \varepsilon_1, \dots, \varepsilon_r \rangle$. -/
noncomputable def unitsLinearMap : (Fin (rank K) → ℤ_[p]) →ₗ[ℤ_[p]] U₁ K p :=
  Fintype.linearCombination ℤ_[p] fun i ↦ diag K p (toE₁ ε hone i)

@[category API, AMS 11]
theorem unitsLinearMap_apply (a : Fin (rank K) → ℤ_[p]) :
    unitsLinearMap ε hone a = ∑ i, a i • diag K p (toE₁ ε hone i) :=
  Fintype.linearCombination_apply ℤ_[p] _ a

@[category API, AMS 11]
theorem coe_unitsLinearMap_apply (a : Fin (rank K) → ℤ_[p]) (v : PrimesAbove K p) :
    (((unitsLinearMap ε hone a v).toMul : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) =
      ∏ i, OneUnits.zpPow (algebraMap (𝓞 K) (v.1.adicCompletion K) (ε i : 𝓞 K)) (a i) := by
  rw [unitsLinearMap_apply, Finset.sum_apply, toMul_sum]
  push_cast
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Pi.smul_apply, OneUnits.coe_smul]
  rfl

/-- $\prod_i \varepsilon_i^{a_i.\mathrm{appr}\, n} \to \prod_i \varepsilon_i^{a_i}$ in
$K_\mathfrak{p}$: the reading of $\mathbb{Z}_p$-powers of [Nelson, Lemma 4.2]. -/
@[category API, AMS 11]
theorem tendsto_prod_pow_appr (a : Fin (rank K) → ℤ_[p]) (v : PrimesAbove K p) :
    Tendsto (fun n : ℕ ↦ ((∏ i, (ε i : K) ^ (a i).appr n : K) : v.1.adicCompletion K)) atTop
      (𝓝 (((unitsLinearMap ε hone a v).toMul : (v.1.adicCompletion K)ˣ) :
        v.1.adicCompletion K)) := by
  rw [coe_unitsLinearMap_apply]
  have hconv : ∀ n : ℕ, ((∏ i, (ε i : K) ^ (a i).appr n : K) : v.1.adicCompletion K)
      = ∏ i, (algebraMap (𝓞 K) (v.1.adicCompletion K) (ε i : 𝓞 K)) ^ (a i).appr n := by
    intro n
    rw [coe_prod_pow, coe_coe_adicCompletion]
    push_cast
    rfl
  refine Tendsto.congr (fun n ↦ (hconv n).symm) ?_
  exact tendsto_finsetProd _ fun i _ ↦
    OneUnits.tendsto_pow_appr (norm_algebraMap_sub_one_lt K p (hone i) v) (a i)

/-- `IsPadicRelation K p ε a` says exactly $\varphi_\varepsilon(a) = 0$. -/
@[category API, AMS 11]
theorem isPadicRelation_iff (a : Fin (rank K) → ℤ_[p]) :
    IsPadicRelation K p ε a ↔ unitsLinearMap ε hone a = 0 := by
  constructor
  · intro h
    funext v
    refine OneUnits.ext_of_coe ?_
    rw [← tendsto_nhds_unique (h v.1 v.2) (tendsto_prod_pow_appr ε hone a v)]
    rfl
  · intro h v hv
    have h1 := tendsto_prod_pow_appr ε hone a ⟨v, hv⟩
    have h2 : (((unitsLinearMap ε hone a ⟨v, hv⟩).toMul : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1 := by
      rw [h]
      rfl
    rwa [h2] at h1

@[category API, AMS 11]
theorem range_unitsLinearMap_le : LinearMap.range (unitsLinearMap ε hone) ≤ closureE₁ K p := by
  rw [unitsLinearMap, Fintype.range_linearCombination, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact AddSubgroup.le_topologicalClosure _ (AddMonoidHom.mem_range.2 ⟨_, rfl⟩)

@[category API, AMS 11]
theorem continuous_unitsLinearMap : Continuous (unitsLinearMap ε hone) := by
  have h : ⇑(unitsLinearMap ε hone) = fun a ↦ ∑ i, a i • diag K p (toE₁ ε hone i) :=
    funext (unitsLinearMap_apply ε hone)
  rw [h]
  refine continuous_pi fun v ↦ ?_
  simp only [Finset.sum_apply]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  simp only [Pi.smul_apply]
  exact (OneUnits.continuous_smul_const _).comp (continuous_apply i)

/-- The image of the compact group $\mathbb{Z}_p^r$ is closed. -/
@[category API, AMS 11]
theorem isClosed_range_unitsLinearMap :
    IsClosed (LinearMap.range (unitsLinearMap ε hone) : Set (U₁ K p)) := by
  rw [LinearMap.coe_range]
  exact (isCompact_range (continuous_unitsLinearMap ε hone)).isClosed

/-- With $N$ the index of $\langle \varepsilon_i \rangle$ in $\mathcal{O}_K^\times$, every
$u \in E_1$ has $u^N = \prod_i \varepsilon_i^{c_i}$ with $c \in \mathbb{Z}^r$, so
$N \cdot u \in \varphi_\varepsilon(\mathbb{Z}_p^r)$. -/
@[category API, AMS 11]
theorem index_smul_diag_mem_range (u : Additive (E₁ K p)) :
    ((Subgroup.closure (Set.range ε)).index : ℤ_[p]) • diag K p u ∈
      LinearMap.range (unitsLinearMap ε hone) := by
  classical
  set N := (Subgroup.closure (Set.range ε)).index with hN
  obtain ⟨c, hc⟩ := Subgroup.mem_closure_range_iff_of_fintype.1
    (Subgroup.pow_index_mem (Subgroup.closure (Set.range ε)) (u.toMul : (𝓞 K)ˣ))
  have hstep : N • u = ∑ i, c i • toE₁ ε hone i := by
    refine Additive.toMul.injective (Subtype.ext ?_)
    rw [toMul_nsmul, toMul_sum]
    push_cast
    rw [hc]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [toMul_zsmul]; rfl
  have hnat : ((N : ℤ_[p]) • diag K p u) = diag K p (N • u) := by
    rw [map_nsmul, U₁.natCast_smul]
  refine ⟨fun i ↦ (c i : ℤ_[p]), ?_⟩
  rw [unitsLinearMap_apply, hnat, hstep, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_zsmul, U₁.intCast_smul]

/-- $N \cdot \overline{E_1} \subseteq \varphi_\varepsilon(\mathbb{Z}_p^r)$. -/
@[category API, AMS 11]
theorem index_smul_mem_range {y : U₁ K p} (hy : y ∈ closureE₁ K p) :
    ((Subgroup.closure (Set.range ε)).index : ℤ_[p]) • y ∈
      LinearMap.range (unitsLinearMap ε hone) := by
  set N := (Subgroup.closure (Set.range ε)).index with hN
  have hy' : y ∈ closure (Set.range (diag K p)) := by rwa [← coe_closureE₁]
  have h1 : (N : ℤ_[p]) • y ∈ closure ((fun z ↦ (N : ℤ_[p]) • z) '' Set.range (diag K p)) :=
    image_closure_subset_closure_image (continuous_const_smul _) ⟨y, hy', rfl⟩
  have h2 : (fun z ↦ (N : ℤ_[p]) • z) '' Set.range (diag K p)
      ⊆ (LinearMap.range (unitsLinearMap ε hone) : Set (U₁ K p)) := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact index_smul_diag_mem_range ε hone u
  exact (isClosed_range_unitsLinearMap ε hone).closure_subset_iff.2 h2 h1

/-- $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}
= \operatorname{rank}_{\mathbb{Z}_p} \varphi_\varepsilon(\mathbb{Z}_p^r)$: the image has finite
index in the closure. -/
@[category API, AMS 11]
theorem rank_closureE₁_eq (hmax : IsMaxRank ε) :
    Module.rank ℤ_[p] (closureE₁ K p) =
      Module.rank ℤ_[p] (LinearMap.range (unitsLinearMap ε hone)) := by
  have hfi := Units.isMaxRank_iff_closure_finiteIndex.1 hmax
  have hc : ((Subgroup.closure (Set.range ε)).index : ℤ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.2 hfi.index_ne_zero
  exact (rank_eq_of_le_of_smul_le (range_unitsLinearMap_le ε hone) hc
    fun y hy ↦ index_smul_mem_range ε hone hy).symm

/-- Rank–nullity for $\varphi_\varepsilon : \mathbb{Z}_p^r \to U_1$. The kernel lives in `Type`
and the range in the universe of `K`, hence the `Cardinal.lift`. -/
@[category API, AMS 11]
theorem rank_range_add_rank_ker_unitsLinearMap :
    Module.rank ℤ_[p] (LinearMap.range (unitsLinearMap ε hone)) +
      Cardinal.lift (Module.rank ℤ_[p] (LinearMap.ker (unitsLinearMap ε hone))) = rank K := by
  have h := LinearMap.lift_rank_range_add_rank_ker (unitsLinearMap ε hone)
  rw [rank_fin_fun] at h
  simpa using h

/-- The kernel of $\varphi_\varepsilon$, a submodule of the free module $\mathbb{Z}_p^r$, has rank
zero iff it is zero, i.e. iff every $p$-adic relation among the $\varepsilon_i$ is trivial. -/
@[category API, AMS 11]
theorem rank_ker_unitsLinearMap_eq_zero_iff :
    Module.rank ℤ_[p] (LinearMap.ker (unitsLinearMap ε hone)) = 0 ↔
      ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0 := by
  rw [rank_zero_iff_forall_zero]
  constructor
  · intro h a ha
    exact congrArg Subtype.val
      (h ⟨a, (isPadicRelation_iff ε hone a).1 ha⟩ : (⟨a, _⟩ : LinearMap.ker _) = 0)
  · rintro h ⟨a, ha⟩
    exact Subtype.ext (h a ((isPadicRelation_iff ε hone a).2 ha))

include hone in
/-- For a fixed admissible family $\varepsilon$, the $\mathbb{Z}_p$-rank form of the conjecture is
the statement that $\varphi_\varepsilon$ is injective. -/
@[category API, AMS 11]
theorem finrank_closureE₁_eq_iff (hmax : IsMaxRank ε) :
    Module.finrank ℤ_[p] (closureE₁ K p) = rank K ↔
      ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0 := by
  have hsum := rank_range_add_rank_ker_unitsLinearMap ε hone
  have hA : Module.rank ℤ_[p] (LinearMap.range (unitsLinearMap ε hone)) < Cardinal.aleph0 :=
    lt_of_le_of_lt le_self_add (hsum ▸ Cardinal.natCast_lt_aleph0)
  have hB : Module.rank ℤ_[p] (LinearMap.ker (unitsLinearMap ε hone)) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.1 (lt_of_le_of_lt le_add_self (hsum ▸ Cardinal.natCast_lt_aleph0))
  obtain ⟨na, ha⟩ := Cardinal.lt_aleph0.1 hA
  obtain ⟨nb, hb⟩ := Cardinal.lt_aleph0.1 hB
  rw [ha, hb, Cardinal.lift_natCast, ← Nat.cast_add] at hsum
  have hab : na + nb = rank K := by exact_mod_cast hsum
  rw [Module.finrank_eq_of_rank_eq ((rank_closureE₁_eq ε hone hmax).trans ha),
    ← rank_ker_unitsLinearMap_eq_zero_iff ε hone, hb, Nat.cast_eq_zero]
  omega

end equivalence

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
The $\mathbb{Z}_p$-rank form `leopoldt_conjecture.variants.zpRank` is equivalent to the
formulation of `leopoldt_conjecture`: injectivity of $\varphi_\varepsilon$ for every family
$\varepsilon$ of units of maximal rank lying in $E_1$. One direction uses that such a family
exists (`exists_isMaxRank_isPrincipalUnitAbove`); the other that the rank of $\overline{E_1}$
does not depend on the family (`finrank_closureE₁_eq_iff`).
-/
@[category API, AMS 11]
theorem zpRank_iff :
    Module.finrank ℤ_[p] (closureE₁ K p) = rank K ↔
      ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
        ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0 := by
  refine ⟨fun h ε hmax hone ↦ (finrank_closureE₁_eq_iff ε hone hmax).1 h, fun h ↦ ?_⟩
  obtain ⟨ε, hmax, hone⟩ := exists_isMaxRank_isPrincipalUnitAbove K p
  exact (finrank_closureE₁_eq_iff ε hone hmax).2 (h ε hmax hone)

end Leopoldt
