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

import FormalConjecturesUtil
import FormalConjectures.Wikipedia.LeopoldtConjecture
import FormalConjectures.Wikipedia.LeopoldtConjecture.ZpRank
import FormalConjecturesTest.LeopoldtCMProof.Statement
import FormalConjecturesTest.LeopoldtCMProof.Bridge

/-!
# Mihăilescu's Leopoldt defect is Wikipedia's Leopoldt defect

`Mihailescu.LeopoldtConjecture p K` says that the Leopoldt defect
$\mathcal{D}_L(K) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E})$ vanishes,
where $\overline{E} = \bigcap_{n > 0} \iota(E) \cdot U^{p^n}$ is the `p`-adic closure of the
global units in the semilocal units $U$ and the $\mathbb{Z}_p$-rank is `Mihailescu.zpRankBelow`,
the largest $n$ such that $\mathbb{Z}_p^n$ embeds continuously into $\overline{E}$.
`leopoldt_conjecture.variants.zpRank` says that
$\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} = r_1 + r_2 - 1$ for the closure
`closureE₁ K p` of $E_1$ in the principal units $U_1$.

The main result `Mihailescu.zpRankBelow_unitClosure_eq` is that the two ranks agree,
$$\mathbb{Z}_p\text{-rk}(\overline{E}) = \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1},$$
so that `Mihailescu.defect p K = rank K - Module.finrank ℤ_[p] (closureE₁ K p)`
(`Mihailescu.defect_eq`) and the two conjectures are equivalent
(`Mihailescu.leopoldtConjecture_iff_finrank`).

* $\le$: a continuous injection $f : \mathbb{Z}_p^n \to \overline{E}$ has $f^N$ landing in
  $U_1$ for the exponent $N$ of $U / U_1$ (`exists_pow_mem_range_toSemilocalUnits`), and then
  in $\overline{E_1}$ (`mem_closureE₁_of_forall_exists`); a continuous additive map
  $\mathbb{Z}_p^n \to U_1$ is $\mathbb{Z}_p$-linear (`map_smul_of_continuous`), and an injective
  linear map bounds the rank.
* $\ge$: the image of $\varphi_\varepsilon : \mathbb{Z}_p^r \to U_1$ has the rank of
  $\overline{E_1}$ (`rank_closureE₁_eq`), so it contains a free submodule of that rank, and
  $\varphi_\varepsilon(\mathbb{Z}_p^r) \subseteq \overline{E}$
  (`toSemilocalUnits_unitsLinearMap_mem_unitClosure`).
-/

open Filter IsDedekindDomain NumberField NumberField.Units Topology

open scoped NumberField Valued

namespace Leopoldt

/- ## The supremum defining `zpRankBelow` -/

section zpRankBelow

variable {p : ℕ} [Fact p.Prime] {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- `n ≤ zpRankBelow p bound H` as soon as `n ≤ bound` and `ℤ_p^n` embeds continuously into
`H`. -/
@[category API, AMS 11]
theorem le_zpRankBelow_of_exists {bound n : ℕ} (hn : n ≤ bound) {H : Subgroup G}
    (f : Multiplicative (Fin n → ℤ_[p]) →* G) (hf : Function.Injective f) (hc : Continuous f)
    (hH : ∀ x, f x ∈ H) : n ≤ Mihailescu.zpRankBelow p bound H :=
  le_csSup ⟨bound, fun _ hk ↦ hk.1⟩ ⟨hn, f, hf, hc, hH⟩

/-- `zpRankBelow p bound H ≤ m` if `n ≤ m` for every `n` such that `ℤ_p^n` embeds continuously
into `H`. The set of such `n` is never empty since `n = 0` qualifies. -/
@[category API, AMS 11]
theorem zpRankBelow_le {bound m : ℕ} {H : Subgroup G}
    (h : ∀ n : ℕ, ∀ f : Multiplicative (Fin n → ℤ_[p]) →* G, Function.Injective f →
      Continuous f → (∀ x, f x ∈ H) → n ≤ m) :
    Mihailescu.zpRankBelow p bound H ≤ m := by
  have hone : Continuous ⇑(1 : Multiplicative (Fin 0 → ℤ_[p]) →* G) := continuous_const
  refine csSup_le ⟨0, Nat.zero_le _, 1, Function.injective_of_subsingleton _, hone,
    fun _ ↦ H.one_mem⟩ ?_
  rintro n ⟨-, f, hf, hc, hH⟩
  exact h n f hf hc hH

end zpRankBelow

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/- ## Ranks -/

/-- $r_1 + r_2 - 1 \le r_1 + 2 r_2 = [K : \mathbb{Q}]$. -/
@[category API, AMS 11]
theorem rank_le_finrank : rank K ≤ Module.finrank ℚ K := by
  have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  show Fintype.card (InfinitePlace K) - 1 ≤ Module.finrank ℚ K
  lia

/-- $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} \le r_1 + r_2 - 1$. Rank-nullity for
$\varphi_\varepsilon : \mathbb{Z}_p^r \to U_1$, whose image has the same rank as
$\overline{E_1}$ because it has finite index in it. -/
@[category API, AMS 11]
theorem rank_closureE₁_le : Module.rank ℤ_[p] (closureE₁ K p) ≤ (rank K : Cardinal) := by
  obtain ⟨ε, hmax, hone⟩ := exists_isMaxRank_isPrincipalUnitAbove K p
  rw [rank_closureE₁_eq ε hone hmax, ← rank_range_add_rank_ker_unitsLinearMap ε hone]
  exact le_self_add

/-- $\overline{E_1}$ has finite $\mathbb{Z}_p$-rank. -/
@[category API, AMS 11]
theorem rank_closureE₁_lt_aleph0 : Module.rank ℤ_[p] (closureE₁ K p) < Cardinal.aleph0 :=
  (rank_closureE₁_le K p).trans_lt Cardinal.natCast_lt_aleph0

/-- $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} \le r_1 + r_2 - 1$, as naturals. -/
@[category API, AMS 11]
theorem finrank_closureE₁_le_rank : Module.finrank ℤ_[p] (closureE₁ K p) ≤ rank K :=
  Module.finrank_le_of_rank_le (rank_closureE₁_le K p)

/- ## The rank of `unitClosure` is at most the rank of `closureE₁` -/

variable {K p}

/-- A continuous additive map $\mathbb{Z}_p^n \to U_1$ is $\mathbb{Z}_p$-linear, since
$a \cdot x = \lim (a.\mathrm{appr}\,k) \cdot x$ on both sides (`tendsto_appr_nsmul`). -/
@[category API, AMS 11]
theorem map_smul_of_continuous {n : ℕ} (g : (Fin n → ℤ_[p]) →+ U₁ K p) (hg : Continuous g)
    (a : ℤ_[p]) (x : Fin n → ℤ_[p]) : g (a • x) = a • g x := by
  have h1 : Tendsto (fun k ↦ g ((a.appr k : ℤ_[p]) • x)) atTop (𝓝 (g (a • x))) :=
    (hg.tendsto _).comp ((PadicInt.tendsto_appr a).smul_const x)
  have h2 : Tendsto (fun k ↦ a.appr k • g x) atTop (𝓝 (a • g x)) :=
    tendsto_appr_nsmul K p a (g x)
  refine tendsto_nhds_unique (h1.congr fun k ↦ ?_) h2
  rw [Nat.cast_smul_eq_nsmul, map_nsmul]

/-- If $u^N \in U_1$ for all $u \in U$, a continuous homomorphism $f : \mathbb{Z}_p^n \to U$
lifts, after raising to the $N$-th power, to a continuous additive map $g : \mathbb{Z}_p^n \to U_1$
with $\iota(g(x)) = f(x)^N$. -/
@[category API, AMS 11]
theorem exists_addMonoidHom_of_pow_mem_range {n N : ℕ}
    (hN : ∀ w : Mihailescu.SemilocalUnits p K, w ^ N ∈ (toSemilocalUnits K p).range)
    (f : Multiplicative (Fin n → ℤ_[p]) →* Mihailescu.SemilocalUnits p K) (hc : Continuous f) :
    ∃ g : (Fin n → ℤ_[p]) →+ U₁ K p, Continuous g ∧
      ∀ x, toSemilocalUnits K p (Multiplicative.ofAdd (g x)) = f (Multiplicative.ofAdd x) ^ N := by
  have hesymm : Continuous
      ⇑(MonoidHom.ofInjective (toSemilocalUnits_injective K p)).symm := by
    rw [(isInducing_toSemilocalUnits K p).continuous_iff]
    exact continuous_subtype_val.congr fun y ↦
      (MonoidHom.apply_ofInjective_symm (toSemilocalUnits_injective K p) y).symm
  refine ⟨AddMonoidHom.toMultiplicative.symm
    ((MonoidHom.ofInjective (toSemilocalUnits_injective K p)).symm.toMonoidHom.comp
      (((powMonoidHom N).comp f).codRestrict _ fun x ↦ hN _)), ?_, fun x ↦ ?_⟩
  · exact hesymm.comp (((continuous_pow N).comp hc).subtype_mk _)
  · exact MonoidHom.apply_ofInjective_symm (toSemilocalUnits_injective K p) _

/-- If $w \in \overline{E} = \bigcap_n \iota(E) \cdot U^{p^{n+1}}$ and $u^N \in U_1$ for all
$u \in U$, then the element $y \in U_1$ with $\iota(y) = w^N$ lies in $\overline{E_1}$: from
$w = \iota(e) \cdot u^{p^{n+1}}$ one gets $y = \iota(e^N) + p^{n+1} \cdot z$ with $e^N \in E_1$
and $\iota(z) = u^N$. -/
@[category API, AMS 11]
theorem mem_closureE₁_of_toSemilocalUnits_eq_pow {N : ℕ}
    (hN : ∀ w : Mihailescu.SemilocalUnits p K, w ^ N ∈ (toSemilocalUnits K p).range)
    {w : Mihailescu.SemilocalUnits p K} (hw : w ∈ Mihailescu.unitClosure p K) {y : U₁ K p}
    (hy : toSemilocalUnits K p (Multiplicative.ofAdd y) = w ^ N) : y ∈ closureE₁ K p := by
  have hpr : ∀ x : (𝓞 K)ˣ, Mihailescu.diagonalUnits p K x ∈ (toSemilocalUnits K p).range →
      IsPrincipalUnitAbove K p x := by
    intro x hx
    refine isPrincipalUnitAbove_of_forall_valued_sub_one_lt K p fun v ↦ ?_
    have h := (mem_range_toIntegerUnits_iff v.1 _).1
      ((mem_range_toSemilocalUnits_iff K p _).1 hx v)
    rwa [coe_diagonalUnits_apply K p x v] at h
  refine mem_closureE₁_of_forall_exists K p fun m ↦ ?_
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (Subgroup.mem_iInf.1 hw m)
  obtain ⟨e, rfl⟩ := MonoidHom.mem_range.1 ha
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hb
  have hePow : IsPrincipalUnitAbove K p (e ^ N) :=
    hpr _ (by rw [map_pow]; exact hN _)
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 (hN u)
  set d : U₁ K p := diag K p (Additive.ofMul (⟨e ^ N, hePow⟩ : E₁ K p)) with hd
  have hgoal : toSemilocalUnits K p
      (Multiplicative.ofAdd (d + (p : ℤ_[p]) ^ (m + 1) • z.toAdd)) = w ^ N := by
    rw [ofAdd_add, map_mul, hd, toSemilocalUnits_ofAdd_diag, ← hab, mul_pow]
    congr 1
    · show Mihailescu.diagonalUnits p K (e ^ N) = Mihailescu.diagonalUnits p K e ^ N
      rw [map_pow]
    · rw [← Nat.cast_pow p (m + 1),
        toSemilocalUnits_ofAdd_natCast_smul, ofAdd_toAdd, hz, powMonoidHom_apply,
        ← pow_mul, ← pow_mul, Nat.mul_comm N (p ^ (m + 1))]
  exact ⟨d, ⟨_, rfl⟩, z.toAdd, toSemilocalUnits_injective K p (hy.trans hgoal.symm)⟩

/-- $g$ is injective when $f$ is and $N \ne 0$: $g(x) = 0$ gives $f(x)^N = f(N x) = 1$, so
$N x = 0$ and $x = 0$ in the torsion-free group $\mathbb{Z}_p^n$. -/
@[category API, AMS 11]
theorem injective_of_toSemilocalUnits_eq_pow {n N : ℕ} (hN0 : N ≠ 0)
    (f : Multiplicative (Fin n → ℤ_[p]) →* Mihailescu.SemilocalUnits p K)
    (hf : Function.Injective f) (g : (Fin n → ℤ_[p]) →+ U₁ K p)
    (hg : ∀ x, toSemilocalUnits K p (Multiplicative.ofAdd (g x)) =
      f (Multiplicative.ofAdd x) ^ N) :
    Function.Injective g := by
  refine (injective_iff_map_eq_zero g).2 fun x hx ↦ ?_
  have h1 : f (Multiplicative.ofAdd x) ^ N = 1 := by
    rw [← hg x, hx]
    exact map_one _
  have h2 : f (Multiplicative.ofAdd (N • x)) = f 1 := by
    rw [ofAdd_nsmul, map_pow, h1, map_one]
  have h3 : (N : ℤ_[p]) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact Multiplicative.ofAdd.injective (hf h2)
  exact (smul_eq_zero.1 h3).resolve_left (Nat.cast_ne_zero.2 hN0)

/-- An injective linear map $\mathbb{Z}_p^n \to \overline{E_1}$ forces
$n \le \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$. -/
@[category API, AMS 11]
theorem le_finrank_closureE₁_of_linearMap {n : ℕ} (g : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] U₁ K p)
    (hg : Function.Injective g) (hr : LinearMap.range g ≤ closureE₁ K p) :
    n ≤ Module.finrank ℤ_[p] (closureE₁ K p) := by
  have hginj : Function.Injective
      (LinearMap.codRestrict (closureE₁ K p) g fun x ↦ hr (LinearMap.mem_range_self g x)) :=
    fun a b hab ↦ hg (congrArg Subtype.val hab)
  have hrank := Module.finrank_le_finrank_of_rank_le_rank
    (LinearMap.lift_rank_le_of_injective _ hginj) (rank_closureE₁_lt_aleph0 K p)
  rwa [Module.finrank_fin_fun] at hrank

/-- A continuous injective homomorphism $\mathbb{Z}_p^n \to U$ with image in $\overline{E}$ forces
$n \le \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$. -/
@[category API, AMS 11]
theorem le_finrank_closureE₁_of_monoidHom {n : ℕ}
    (f : Multiplicative (Fin n → ℤ_[p]) →* Mihailescu.SemilocalUnits p K)
    (hf : Function.Injective f) (hc : Continuous f)
    (hr : ∀ x, f x ∈ Mihailescu.unitClosure p K) :
    n ≤ Module.finrank ℤ_[p] (closureE₁ K p) := by
  obtain ⟨N, hN0, hN⟩ := exists_pow_mem_range_toSemilocalUnits K p
  obtain ⟨g, hgc, hg⟩ := exists_addMonoidHom_of_pow_mem_range hN f hc
  refine le_finrank_closureE₁_of_linearMap
    { toFun := g
      map_add' := map_add g
      map_smul' := fun a x ↦ map_smul_of_continuous g hgc a x }
    (injective_of_toSemilocalUnits_eq_pow hN0 f hf g hg) ?_
  rintro _ ⟨x, rfl⟩
  exact mem_closureE₁_of_toSemilocalUnits_eq_pow hN (hr (Multiplicative.ofAdd x)) (hg x)

variable (K p)

/-- $\mathbb{Z}_p\text{-rk}(\overline{E}) \le \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$,
for any bound on the supremum. -/
@[category API, AMS 11]
theorem zpRankBelow_unitClosure_le (bound : ℕ) :
    Mihailescu.zpRankBelow p bound (Mihailescu.unitClosure p K) ≤
      Module.finrank ℤ_[p] (closureE₁ K p) :=
  zpRankBelow_le fun _ f hf hc hr ↦ le_finrank_closureE₁_of_monoidHom f hf hc hr

/- ## The rank of `closureE₁` is at most the rank of `unitClosure` -/

variable {K p}

/-- `rank_closureE₁_eq` for `Module.finrank`. -/
@[category API, AMS 11]
theorem finrank_closureE₁_eq_finrank_range {ε : Fin (rank K) → (𝓞 K)ˣ}
    (hone : ∀ i, IsPrincipalUnitAbove K p (ε i)) (hmax : IsMaxRank ε) :
    Module.finrank ℤ_[p] (closureE₁ K p) =
      Module.finrank ℤ_[p] (LinearMap.range (unitsLinearMap ε hone)) := by
  exact congrArg Cardinal.toNat (rank_closureE₁_eq ε hone hmax)

/-- If the image of a linear map `φ : N →ₗ[R] M` has rank at least `n`, then `R ^ n` embeds
into `N` in such a way that the composite with `φ` is still injective: pick `n` linearly
independent elements of the image and any preimages of them.

Stated over abstract `R`, `N`, `M`: the instance chain of `U₁ K p` (a product of
`ℤ_[p]`-modules built from `Additive (oneUnits _)`) is expensive enough that elaborating this
argument in place exceeds the heartbeat limit. It is a general fact and a candidate for
`FormalConjecturesForMathlib`. -/
@[category API, AMS 11]
theorem exists_linearMap_injective_comp_of_le_finrank_range {R N M : Type*} [Ring R]
    [StrongRankCondition R] [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    (φ : N →ₗ[R] M) {n : ℕ} (hn : n ≤ Module.finrank R (LinearMap.range φ)) :
    ∃ ψ : (Fin n → R) →ₗ[R] N, Function.Injective fun b ↦ φ (ψ b) := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_of_le_finrank hn
  have hy : LinearIndependent R fun j ↦ ((x j : M)) :=
    hx.map' (Submodule.subtype _) (Submodule.ker_subtype _)
  choose a ha using fun j ↦ LinearMap.mem_range.1 (x j).2
  have hval : ∀ b, φ (Fintype.linearCombination R a b) = ∑ j, b j • ((x j : M)) := fun b ↦ by
    rw [Fintype.linearCombination_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, ha j]
  refine ⟨Fintype.linearCombination R a, fun b b' hbb' ↦ ?_⟩
  have hzero : ∀ c, φ (Fintype.linearCombination R a c) = 0 → c = 0 := by
    intro c hc
    rw [hval] at hc
    exact funext fun j ↦ Fintype.linearIndependent_iff.1 hy c hc j
  exact sub_eq_zero.1 (hzero (b - b') (by rw [map_sub, map_sub]; exact sub_eq_zero.2 hbb'))

/-- $\varphi_\varepsilon(\mathbb{Z}_p^r)$ contains a free submodule of any rank $n$ below
$\operatorname{rank}_{\mathbb{Z}_p} \varphi_\varepsilon(\mathbb{Z}_p^r)$: there is a linear
map $\psi : \mathbb{Z}_p^{n} \to \mathbb{Z}_p^r$ with $\varphi_\varepsilon \circ \psi$
injective. -/
@[category API, AMS 11]
theorem exists_linearMap_injective_comp {ε : Fin (rank K) → (𝓞 K)ˣ}
    (hone : ∀ i, IsPrincipalUnitAbove K p (ε i)) {n : ℕ}
    (hn : n ≤ Module.finrank ℤ_[p] (LinearMap.range (unitsLinearMap ε hone))) :
    ∃ ψ : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin (rank K) → ℤ_[p]),
      Function.Injective fun b ↦ unitsLinearMap ε hone (ψ b) :=
  exists_linearMap_injective_comp_of_le_finrank_range _ hn

variable (K p)

/-- $\mathbb{Z}_p^{n}$ embeds continuously into $\overline{E}$ for every
$n \le \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$: compose $\psi$,
$\varphi_\varepsilon$ and $U_1 \subseteq U$. The rank is a parameter rather than being fixed
at $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$ so that `Fin _` never carries an
unevaluated `Module.finrank` through elaboration. -/
@[category API, AMS 11]
theorem exists_monoidHom_unitClosure {n : ℕ}
    (hn : n ≤ Module.finrank ℤ_[p] (closureE₁ K p)) :
    ∃ f : Multiplicative (Fin n → ℤ_[p]) →* Mihailescu.SemilocalUnits p K,
      Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ Mihailescu.unitClosure p K := by
  obtain ⟨ε, hmax, hone⟩ := exists_isMaxRank_isPrincipalUnitAbove K p
  obtain ⟨ψ, hψ⟩ := exists_linearMap_injective_comp hone
    (hn.trans (le_of_eq (finrank_closureE₁_eq_finrank_range hone hmax)))
  refine ⟨(toSemilocalUnits K p).comp (AddMonoidHom.toMultiplicative
    ((unitsLinearMap ε hone).toAddMonoidHom.comp ψ.toAddMonoidHom)), ?_, ?_, ?_⟩
  · exact (toSemilocalUnits_injective K p).comp fun a b hab ↦
      Multiplicative.toAdd.injective (hψ (Multiplicative.ofAdd.injective hab))
  · exact (continuous_toSemilocalUnits K p).comp (continuous_ofAdd.comp
      (((continuous_unitsLinearMap ε hone).comp (LinearMap.continuous_on_pi ψ)).comp
        continuous_toAdd))
  · exact fun x ↦ toSemilocalUnits_unitsLinearMap_mem_unitClosure K p hone (ψ x.toAdd)

/-- $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} \le \mathbb{Z}_p\text{-rk}(\overline{E})$
as soon as the bound is at least $r_1 + r_2 - 1$. -/
@[category API, AMS 11]
theorem finrank_closureE₁_le_zpRankBelow {bound : ℕ} (hb : rank K ≤ bound) :
    Module.finrank ℤ_[p] (closureE₁ K p) ≤
      Mihailescu.zpRankBelow p bound (Mihailescu.unitClosure p K) := by
  obtain ⟨f, hf, hc, hr⟩ := exists_monoidHom_unitClosure K p le_rfl
  exact le_zpRankBelow_of_exists ((finrank_closureE₁_le_rank K p).trans hb) f hf hc hr

/- ## The two Leopoldt defects agree -/

namespace Mihailescu

/-- **The two $\mathbb{Z}_p$-ranks agree.** Mihăilescu's $\mathbb{Z}_p$-rank of
$\overline{E} = \bigcap_{n > 0} \iota(E) \cdot U^{p^n} \subseteq U$ equals the
$\mathbb{Z}_p$-rank of the closure $\overline{E_1}$ of $E_1$ in $U_1$, for any bound at least
$r_1 + r_2 - 1$ on the supremum. -/
@[category API, AMS 11]
theorem zpRankBelow_unitClosure_eq {bound : ℕ} (hb : rank K ≤ bound) :
    Mihailescu.zpRankBelow p bound (Mihailescu.unitClosure p K) =
      Module.finrank ℤ_[p] (closureE₁ K p) :=
  le_antisymm (zpRankBelow_unitClosure_le K p bound) (finrank_closureE₁_le_zpRankBelow K p hb)

/-- **The Leopoldt defects agree**:
$\mathcal{D}_L(K) = (r_1 + r_2 - 1) - \operatorname{rank}_{\mathbb{Z}_p} \overline{E_1}$. -/
@[category API, AMS 11]
theorem defect_eq : Mihailescu.defect p K = rank K - Module.finrank ℤ_[p] (closureE₁ K p) := by
  rw [Mihailescu.defect_eq_sub, zpRankBelow_unitClosure_eq K p (rank_le_finrank K)]

/-- **Mihăilescu's formulation of Leopoldt's conjecture is Wikipedia's**: the Leopoldt defect
vanishes iff $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} = r_1 + r_2 - 1$, the statement
of `leopoldt_conjecture.variants.zpRank`. -/
@[category API, AMS 11]
theorem leopoldtConjecture_iff_finrank :
    Mihailescu.LeopoldtConjecture p K ↔ Module.finrank ℤ_[p] (closureE₁ K p) = rank K := by
  rw [Mihailescu.leopoldtConjecture_iff_defect, defect_eq, Nat.sub_eq_zero_iff_le]
  exact ⟨fun h ↦ le_antisymm (finrank_closureE₁_le_rank K p) h, fun h ↦ h.ge⟩

/-- Mihăilescu's formulation is also equivalent to the `p`-adic-relation form
`leopoldt_conjecture`, by `zpRank_iff`. -/
@[category API, AMS 11]
theorem leopoldtConjecture_iff_forall_isPadicRelation :
    Mihailescu.LeopoldtConjecture p K ↔
      ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
        ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0 :=
  (leopoldtConjecture_iff_finrank K p).trans (zpRank_iff K p)

end Mihailescu

end Leopoldt
