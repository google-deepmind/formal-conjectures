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
import FormalConjecturesTest.LeopoldtCMProof.LocalUnits
import FormalConjecturesTest.LeopoldtCMProof.ResidueField

/-!
# From the principal units `U₁` to the semilocal units `U`

Wikipedia's formulation of Leopoldt's conjecture (`FormalConjectures.Wikipedia.LeopoldtConjecture`)
works inside $U_1 = \prod_{\mathfrak{p} \mid p} U_{1, \mathfrak{p}}$, the principal units,
written additively as the `ℤ_[p]`-module `U₁ K p`. Mihăilescu's formulation
(`FormalConjecturesTest.LeopoldtCMProof.Statement`) works inside the full semilocal unit group
$U = \prod_{\mathfrak{p} \mid p} \mathcal{O}_\mathfrak{p}^\times$, the group
`Mihailescu.SemilocalUnits p K`. This file is the dictionary between the two.

## Main definitions

* `toSemilocalUnits K p : Multiplicative (U₁ K p) →* SemilocalUnits p K`: the inclusion
  $U_1 \subseteq U$.

## Main results

* `toSemilocalUnits K p : Multiplicative (U₁ K p) →* SemilocalUnits p K` is the inclusion
  $U_1 \subseteq U$. It is injective, continuous and inducing, its range is the set of
  $u \in U$ with $u \equiv 1$ at every $\mathfrak{p} \mid p$ (`mem_range_toSemilocalUnits_iff`),
  and it matches the two diagonal embeddings of the global units (`toSemilocalUnits_ofAdd_diag`).
* `exists_pow_mem_range_toSemilocalUnits`: some fixed power $u^N$ of every $u \in U$ is a principal
  unit, $N$ being the order of the finite group $\prod_{\mathfrak{p} \mid p} k_\mathfrak{p}^\times$
  of residue field units.
* `mem_closureE₁_of_forall_exists`: an element of $U_1$ lying in
  $\iota(E_1) + p^{m+1} U_1$ for every $m$ lies in the closure $\overline{E_1}$. This is where the
  uniform pro-`p` convergence $p^m U_1 \to 1$ enters.
* `toSemilocalUnits_unitsLinearMap_mem_unitClosure`: the image of
  $\varphi_\varepsilon(\mathbb{Z}_p^r)$ lies in Mihăilescu's closure
  $\overline{E} = \bigcap_{n > 0} \iota(E) \cdot U^{p^n}$, by writing each exponent as
  $a = a.\mathrm{appr}\,n + p^n c$.
-/

open Filter IsDedekindDomain NumberField NumberField.Units Topology

open scoped NumberField Valued

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
/-- The inclusion $U_1 \hookrightarrow U$ of the principal units into the semilocal units, as a
group homomorphism from the multiplicative version of the `ℤ_[p]`-module `U₁ K p`. -/
noncomputable def toSemilocalUnits : Multiplicative (U₁ K p) →* Mihailescu.SemilocalUnits p K where
  toFun y v := toIntegerUnits v.1 (y.toAdd v).toMul
  map_one' := funext fun v ↦ map_one (toIntegerUnits v.1)
  map_mul' _ _ := funext fun v ↦ map_mul (toIntegerUnits v.1) _ _

omit [Fact p.Prime] in
/-- `toSemilocalUnits` does not move the underlying element of $K_\mathfrak{p}$ at any place;
it only repackages a principal unit as a unit of $\mathcal{O}_\mathfrak{p}$. -/
@[category API, AMS 11]
theorem coe_toSemilocalUnits_apply (y : Multiplicative (U₁ K p)) (v : PrimesAbove K p) :
    ((toSemilocalUnits K p y v : v.1.adicCompletionIntegers K) : v.1.adicCompletion K) =
      (((y.toAdd v).toMul : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) :=
  coe_toIntegerUnits_apply v.1 _

omit [Fact p.Prime] in
/-- $U_1 \subseteq U$ is injective, being an inclusion place by place. -/
@[category API, AMS 11]
theorem toSemilocalUnits_injective : Function.Injective (toSemilocalUnits K p) := by
  intro y z h
  exact Multiplicative.toAdd.injective
    (funext fun v ↦ Additive.toMul.injective (toIntegerUnits_injective v.1 (congrFun h v)))

omit [Fact p.Prime] in
/-- $U_1 \subseteq U$ is continuous; both carry the product topology, and at each place the
inclusion is `continuous_toIntegerUnits`. -/
@[category API, AMS 11]
theorem continuous_toSemilocalUnits : Continuous (toSemilocalUnits K p) :=
  continuous_pi fun v ↦ (continuous_toIntegerUnits v.1).comp
    (continuous_toMul.comp ((continuous_apply v).comp continuous_toAdd))

omit [Fact p.Prime] in
/-- `U₁` carries the subspace topology of `U`: both are induced from
$\prod_{\mathfrak{p} \mid p} K_\mathfrak{p}$. -/
@[category API, AMS 11]
theorem isInducing_toSemilocalUnits : Topology.IsInducing (toSemilocalUnits K p) := by
  have hg : Continuous fun w : Mihailescu.SemilocalUnits p K ↦
      fun v : PrimesAbove K p ↦ ((w v : v.1.adicCompletionIntegers K) : v.1.adicCompletion K) :=
    continuous_pi fun v ↦
      continuous_subtype_val.comp (Units.continuous_val.comp (continuous_apply v))
  refine Topology.IsInducing.of_comp (continuous_toSemilocalUnits K p) hg ?_
  have heq : (fun w : Mihailescu.SemilocalUnits p K ↦
      fun v : PrimesAbove K p ↦ ((w v : v.1.adicCompletionIntegers K) : v.1.adicCompletion K))
      ∘ toSemilocalUnits K p
      = Pi.map fun v : PrimesAbove K p ↦ fun z : Additive (oneUnits (v.1.adicCompletion K)) ↦
          ((z.toMul : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) := by
    funext y v
    exact coe_toSemilocalUnits_apply K p y v
  rw [heq]
  exact Topology.IsInducing.piMap fun v ↦ OneUnits.isInducing_coe

omit [Fact p.Prime] in
/-- The image of $U_1$ in $U$: a semilocal unit is principal exactly when it is principal at
every $\mathfrak{p} \mid p$. -/
@[category API, AMS 11]
theorem mem_range_toSemilocalUnits_iff (w : Mihailescu.SemilocalUnits p K) :
    w ∈ (toSemilocalUnits K p).range ↔
      ∀ v : Mihailescu.PrimesOver p K, w v ∈ (toIntegerUnits v.1).range := by
  rw [MonoidHom.mem_range]
  refine ⟨fun ⟨y, hy⟩ v ↦ ⟨(y.toAdd v).toMul, by rw [← hy]; rfl⟩, fun h ↦ ?_⟩
  choose u hu using h
  exact ⟨Multiplicative.ofAdd fun v ↦ Additive.ofMul (u v), funext hu⟩

omit [Fact p.Prime] in
/-- The value of the diagonal embedding $E \to U$ at $\mathfrak{p}$, inside $K_\mathfrak{p}$. -/
@[category API, AMS 11]
theorem coe_diagonalUnits_apply (x : (𝓞 K)ˣ) (v : Mihailescu.PrimesOver p K) :
    ((Mihailescu.diagonalUnits p K x v : v.1.adicCompletionIntegers K) : v.1.adicCompletion K)
      = algebraMap (𝓞 K) (v.1.adicCompletion K) (x : 𝓞 K) := by
  rw [show Mihailescu.diagonalUnits p K x v =
    Units.map (algebraMap (𝓞 K) (v.1.adicCompletionIntegers K)).toMonoidHom x from rfl,
    Units.coe_map]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_adicCompletionIntegers K v.1 _

omit [Fact p.Prime] in
/-- The diagonal embedding $E_1 \to U_1$ followed by $U_1 \subseteq U$ is the diagonal embedding
$E \to U$. -/
@[category API, AMS 11]
theorem toSemilocalUnits_ofAdd_diag (u : Additive (E₁ K p)) :
    toSemilocalUnits K p (Multiplicative.ofAdd (diag K p u)) =
      Mihailescu.diagonalUnits p K (u.toMul : (𝓞 K)ˣ) := by
  funext v
  refine Units.ext (Subtype.ext ?_)
  rw [coe_toSemilocalUnits_apply, toAdd_ofAdd, coe_diag_apply]
  rfl

/-- Integer `p`-adic powers become ordinary powers in `U`. -/
@[category API, AMS 11]
theorem toSemilocalUnits_ofAdd_natCast_smul (n : ℕ) (y : U₁ K p) :
    toSemilocalUnits K p (Multiplicative.ofAdd ((n : ℤ_[p]) • y)) =
      toSemilocalUnits K p (Multiplicative.ofAdd y) ^ n := by
  rw [U₁.natCast_smul, ofAdd_nsmul, map_pow]

/-- A fixed power of every semilocal unit is a principal unit: with $N$ the order of the finite
group $\prod_{\mathfrak{p} \mid p} (\mathcal{O}_\mathfrak{p} / \mathfrak{p})^\times$, every
$u \in U$ has $u^N \equiv 1$ modulo every $\mathfrak{p} \mid p$. The exponent kills the
residue-field unit group directly, via `mem_range_toIntegerUnits_iff_residue`. -/
@[category API, AMS 11]
theorem exists_pow_mem_range_toSemilocalUnits :
    ∃ N : ℕ, N ≠ 0 ∧
      ∀ w : Mihailescu.SemilocalUnits p K, w ^ N ∈ (toSemilocalUnits K p).range := by
  set N := Nat.card (∀ v : Mihailescu.PrimesOver p K,
    (IsLocalRing.ResidueField (v.1.adicCompletionIntegers K))ˣ)
  refine ⟨N, Nat.card_pos.ne', fun w ↦ (mem_range_toSemilocalUnits_iff K p _).2 fun v ↦ ?_⟩
  refine (mem_range_toIntegerUnits_iff_residue v.1 _).2 ?_
  have key : (fun v : Mihailescu.PrimesOver p K ↦
      Units.map (IsLocalRing.residue (v.1.adicCompletionIntegers K)).toMonoidHom (w v)) ^ N = 1 :=
    pow_card_eq_one'
  have h2 : Units.map (IsLocalRing.residue (v.1.adicCompletionIntegers K)).toMonoidHom (w v) ^ N
      = 1 := congrFun key v
  rwa [← map_pow] at h2

omit [Fact p.Prime] in
/-- A global unit which is a principal unit in every $K_\mathfrak{p}$, $\mathfrak{p} \mid p$, lies
in $E_1$. This is the converse of `norm_algebraMap_sub_one_lt`. -/
@[category API, AMS 11]
theorem isPrincipalUnitAbove_of_forall_valued_sub_one_lt {u : (𝓞 K)ˣ}
    (h : ∀ v : PrimesAbove K p,
      Valued.v (algebraMap (𝓞 K) (v.1.adicCompletion K) (u : 𝓞 K) - 1) < 1) :
    IsPrincipalUnitAbove K p u := by
  intro v hv
  have hv' := Valued.toNormedField.norm_lt_one_iff.2 (h ⟨v, hv⟩)
  rw [← map_one (algebraMap (𝓞 K) (v.adicCompletion K)), ← map_sub] at hv'
  exact (FinitePlace.norm_lt_one_iff_mem K v ((u : 𝓞 K) - 1)).1 hv'

/-- The subgroups $p^k U_1$ shrink to $0$ uniformly: every neighbourhood of $0$ in $U_1$ contains
$p^k U_1$ for all large $k$. -/
@[category API, AMS 11]
theorem exists_forall_pow_smul_mem {V : Set (U₁ K p)} (hV : V ∈ 𝓝 (0 : U₁ K p)) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ z : U₁ K p, (p : ℤ_[p]) ^ k • z ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, hI, t, ht, hIV⟩ := hV
  have hplace : ∀ v : PrimesAbove K p, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∀ z : Additive (oneUnits (v.1.adicCompletion K)), (p : ℤ_[p]) ^ k • z ∈ t v := by
    intro v
    obtain ⟨s, hs, hst⟩ := Filter.mem_comap.1
      ((OneUnits.isInducing_coe (K := v.1.adicCompletion K)).nhds_eq_comap 0 ▸ ht v)
    obtain ⟨k₀, hk₀⟩ := exists_forall_pow_pow_mem_nhds_one v.1 (norm_natCast_lt_one K p v) hs
    refine ⟨k₀, fun k hk z ↦ hst ?_⟩
    have hcoe : ((((p : ℤ_[p]) ^ k • z).toMul : (v.1.adicCompletion K)ˣ) :
          v.1.adicCompletion K)
        = ((z.toMul : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) ^ p ^ k := by
      rw [← Nat.cast_pow p k, OneUnits.natCast_smul, toMul_nsmul, SubmonoidClass.coe_pow,
        Units.val_pow_eq_pow_val]
    show ((((p : ℤ_[p]) ^ k • z).toMul : (v.1.adicCompletion K)ˣ) :
      v.1.adicCompletion K) ∈ s
    rw [hcoe]
    exact hk₀ k hk _ (OneUnits.mem_oneUnits_iff.1 z.toMul.2)
  choose kk hkk using hplace
  exact ⟨hI.toFinset.sup kk, fun m hm z ↦ hIV fun v hv ↦
    hkk v m ((Finset.le_sup (hI.mem_toFinset.2 hv)).trans hm) (z v)⟩

/-- $p^{m+1} z_m \to 0$ for every sequence $z_m$ in $U_1$. -/
@[category API, AMS 11]
theorem tendsto_pow_succ_smul (z : ℕ → U₁ K p) :
    Tendsto (fun m ↦ (p : ℤ_[p]) ^ (m + 1) • z m) atTop (𝓝 (0 : U₁ K p)) := by
  refine Filter.tendsto_def.2 fun V hV ↦ ?_
  obtain ⟨k₀, hk₀⟩ := exists_forall_pow_smul_mem K p hV
  exact Filter.mem_atTop_sets.2 ⟨k₀, fun m hm ↦ hk₀ (m + 1) (by lia) (z m)⟩

/-- An element of $U_1$ which lies in $\iota(E_1) + p^{m+1} U_1$ for every $m$ lies in the closure
$\overline{E_1}$ of $\iota(E_1)$. -/
@[category API, AMS 11]
theorem mem_closureE₁_of_forall_exists {y : U₁ K p}
    (h : ∀ m : ℕ, ∃ d ∈ Set.range (diag K p), ∃ z : U₁ K p, y = d + (p : ℤ_[p]) ^ (m + 1) • z) :
    y ∈ closureE₁ K p := by
  choose d hd z hz using h
  rw [← SetLike.mem_coe, coe_closureE₁]
  refine mem_closure_of_tendsto (f := d) (b := atTop) ?_ (Eventually.of_forall hd)
  have hd' : ∀ m, d m = y - (p : ℤ_[p]) ^ (m + 1) • z m := fun m ↦ eq_sub_of_add_eq (hz m).symm
  refine Filter.Tendsto.congr (fun m ↦ (hd' m).symm) ?_
  have hsub : Tendsto (fun m ↦ y - (p : ℤ_[p]) ^ (m + 1) • z m) atTop (𝓝 (y - 0)) :=
    tendsto_const_nhds.sub (tendsto_pow_succ_smul K p z)
  rwa [sub_zero] at hsub

/-- $\varphi_\varepsilon(c) = \prod_i \varepsilon_i^{c_i}$ lies in Mihăilescu's closure
$\bigcap_{n > 0} \iota(E) \cdot U^{p^n}$: writing $c_i = c_i.\mathrm{appr}\,n + p^n d_i$ gives
$\varphi_\varepsilon(c) = \iota(\prod_i \varepsilon_i^{c_i.\mathrm{appr}\,n}) \cdot
\varphi_\varepsilon(d)^{p^n}$. -/
@[category API, AMS 11]
theorem toSemilocalUnits_unitsLinearMap_mem_unitClosure {ε : Fin (rank K) → (𝓞 K)ˣ}
    (hone : ∀ i, IsPrincipalUnitAbove K p (ε i)) (c : Fin (rank K) → ℤ_[p]) :
    toSemilocalUnits K p (Multiplicative.ofAdd (unitsLinearMap ε hone c)) ∈
      Mihailescu.unitClosure p K := by
  refine Subgroup.mem_iInf.2 fun n ↦ ?_
  choose d hd using fun i ↦ PadicInt.exists_eq_appr_add_pow_mul (c i) (n + 1)
  have hc : c = (fun i ↦ ((c i).appr (n + 1) : ℤ_[p])) + (p : ℤ_[p]) ^ (n + 1) • d := by
    funext i
    simpa [Pi.smul_apply, smul_eq_mul] using hd i
  rw [hc, map_add, map_smul, ofAdd_add, map_mul]
  refine Subgroup.mul_mem_sup ?_ ?_
  · have hint : unitsLinearMap ε hone (fun i ↦ ((c i).appr (n + 1) : ℤ_[p]))
        = diag K p (∑ i, (c i).appr (n + 1) • toE₁ ε hone i) := by
      rw [unitsLinearMap_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [U₁.natCast_smul, map_nsmul]
    rw [hint, toSemilocalUnits_ofAdd_diag]
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  · rw [← Nat.cast_pow p (n + 1),
      toSemilocalUnits_ofAdd_natCast_smul]
    exact MonoidHom.mem_range.2 ⟨_, rfl⟩

end Leopoldt
