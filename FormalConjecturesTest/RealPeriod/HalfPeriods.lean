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

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactness.Lindelof
import FormalConjecturesTest.RealPeriod.Uniqueness

/-!
# The zeros of $\wp'$ are the half-periods

For a period lattice $\Lambda$ the derivative $\wp'$ of the Weierstrass function is odd and
$\Lambda$-periodic, so it vanishes at every $z$ with $2z \in \Lambda$. Conversely these are its only
zeros off the lattice: `PeriodPair.derivWeierstrassP_eq_zero_iff`. Classically the converse is
proved by counting: $\wp'$ is an elliptic function of order $3$, so it has exactly three zeros in a
period parallelogram [DLMF 23.3, Pastras §1 "The roots of the cubic polynomial"]. That count needs
the argument principle for elliptic functions, which is not in Mathlib, so the converse is proved
here from the second-order differential equation instead.

* $\wp'' = 6 \wp^2 - g_2 / 2$ off the lattice (`PeriodPair.deriv_derivWeierstrassP`), by
  differentiating $\wp'^2 = 4 \wp^3 - g_2 \wp - g_3$; the identity holds near $0$ by
  `PeriodPair.eventually_deriv_derivWeierstrassP` and propagates to the connected set
  $\mathbb{C} \setminus \Lambda$ by the identity theorem.
* If $\wp'(z_0) = 0$ then $t \mapsto \wp(z_0 + t)$ and $t \mapsto \wp(z_0 - t)$ solve the same
  second-order equation with the same initial data at $t = 0$, so they agree near $t = 0$ by
  uniqueness of solutions (`PeriodPair.eventually_weierstrassP_add_eq_sub`), hence wherever both are
  defined by the identity theorem
  (`PeriodPair.weierstrassP_add_eq_sub_of_derivWeierstrassP_eq_zero`).
* So $2 z_0$ is a period of $\wp$. Since $\wp$ has a pole at $0$ but is analytic at $2 z_0$ unless
  $2 z_0 \in \Lambda$, comparing orders at $0$ gives $2 z_0 \in \Lambda$
  (`PeriodPair.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero`).

*References:*
- [DLMF](https://dlmf.nist.gov/23.3), §23.3(i), equations 23.3.9–23.3.11
- [Pas2017] Georgios Pastras. Four Lectures on Weierstrass Elliptic Function and Applications in
    Classical and Quantum Mechanics, §1 "The Roots of the Cubic Polynomial", equations
    (1.29)–(1.36), https://arxiv.org/abs/1706.07371
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter VI,
    Proposition 3.6(a), https://link.springer.com/book/10.1007/978-0-387-09494-6
-/

open Filter Set Topology

/-- The complement of a countable subset of $\mathbb{C}$ is connected. -/
lemma Complex.isPreconnected_compl_of_countable {s : Set ℂ} (hs : s.Countable) :
    IsPreconnected sᶜ :=
  (hs.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected

namespace PeriodPair

variable (L : PeriodPair)

/- ## Lattice equality -/

/-- $\wp$ depends only on the lattice, not on the choice of periods. -/
lemma weierstrassP_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : ℘[L₁] = ℘[L₂] := by
  unfold weierstrassP
  rw [h]

/-- $\wp'$ depends only on the lattice, not on the choice of periods. -/
lemma derivWeierstrassP_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) :
    ℘'[L₁] = ℘'[L₂] := by
  unfold derivWeierstrassP
  rw [h]

/-- A lattice is countable, being discrete and closed in $\mathbb{C}$. -/
lemma countable_lattice : (L.lattice : Set ℂ).Countable :=
  countable_of_Lindelof_of_discrete (X := L.lattice)

/- ## The differential equations -/

/-- $\wp$ is differentiable off the lattice, with derivative $\wp'$. -/
lemma hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt ℘[L] (℘'[L] z) z := by
  simpa using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt

/-- The second-order differential equation $\wp'' = 6 \wp^2 - g_2 / 2$, off the lattice. Near $0$
this is `PeriodPair.eventually_deriv_derivWeierstrassP`; both sides are analytic on the connected
set $\mathbb{C} \setminus \Lambda$, so the identity theorem gives it everywhere. -/
lemma deriv_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  have hg : AnalyticOnNhd ℂ (fun w ↦ 6 * ℘[L] w ^ 2 - L.g₂ / 2) (L.lattice : Set ℂ)ᶜ := by
    intro w hw
    have hw' := L.analyticOnNhd_weierstrassP w hw
    fun_prop
  obtain ⟨V, hV, hVo, hV0⟩ := eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (L.eventually_notMem_lattice.and
      L.eventually_deriv_derivWeierstrassP))
  obtain ⟨z₀, hz₀V, hz₀⟩ : (V ∩ {(0 : ℂ)}ᶜ).Nonempty :=
    Filter.nonempty_of_mem (Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hV0)) self_mem_nhdsWithin)
  refine (L.analyticOnNhd_derivWeierstrassP.deriv.eqOn_of_preconnected_of_eventuallyEq hg
    (Complex.isPreconnected_compl_of_countable L.countable_lattice) (hV z₀ hz₀V hz₀).1 ?_) hz
  filter_upwards [(hVo.sdiff isClosed_singleton).mem_nhds ⟨hz₀V, hz₀⟩] with w hw
  exact (hV w hw.1 hw.2).2

/-- $\wp'$ is differentiable off the lattice, with derivative $6 \wp^2 - g_2 / 2$. -/
lemma hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
  rw [← L.deriv_derivWeierstrassP hz]
  exact (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt

/- ## The zeros of `℘'` -/

/-- $\wp'$ vanishes at the half-periods: if $2z \in \Lambda$ then
$\wp'(z) = \wp'(z - 2z) = \wp'(-z) = -\wp'(z)$. -/
lemma derivWeierstrassP_eq_zero_of_two_mul_mem {z : ℂ} (h : 2 * z ∈ L.lattice) : ℘'[L] z = 0 := by
  have h1 := L.derivWeierstrassP_sub_coe z ⟨2 * z, h⟩
  rw [show z - ((⟨2 * z, h⟩ : L.lattice) : ℂ) = -z by push_cast; ring,
    L.derivWeierstrassP_neg] at h1
  exact CharZero.eq_neg_self_iff.mp h1.symm

/-- If $\wp'(z_0) = 0$ then $\wp(z_0 + t) = \wp(z_0 - t)$ for real $t$ near $0$: both sides, paired
with their derivatives, solve the first-order system $(u, v)' = (v, 6 u^2 - g_2 / 2)$ with the same
initial value $(\wp(z_0), 0)$, and the vector field is locally Lipschitz. -/
lemma eventually_weierstrassP_add_eq_sub {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) (h : ℘'[L] z₀ = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, ℘[L] (z₀ + t) = ℘[L] (z₀ - t) := by
  set v : ℝ → ℂ × ℂ → ℂ × ℂ := fun _ p ↦ (p.2, 6 * p.1 ^ 2 - L.g₂ / 2)
  set f : ℝ → ℂ × ℂ := fun t ↦ (℘[L] (z₀ + t), ℘'[L] (z₀ + t)) with hf
  set g : ℝ → ℂ × ℂ := fun t ↦ (℘[L] (z₀ - t), -℘'[L] (z₀ - t)) with hg
  -- The vector field is `C¹`, hence locally Lipschitz near the common initial value.
  obtain ⟨K, S, hS, hK⟩ :
      ∃ K, ∃ S ∈ 𝓝 (℘[L] z₀, (0 : ℂ)), LipschitzOnWith K (v 0) S := by
    have hv1 : ContDiff ℂ 1 (v 0) := by fun_prop
    exact hv1.contDiffAt.exists_lipschitzOnWith
  -- Both curves stay off the lattice near `0`.
  have hcont : ∀ᶠ t : ℝ in 𝓝 0, z₀ + (t : ℂ) ∉ L.lattice ∧ z₀ - (t : ℂ) ∉ L.lattice := by
    have hopen := L.isClosed_lattice.isOpen_compl.mem_nhds hz₀
    have h₁ : Filter.Tendsto (fun t : ℝ ↦ z₀ + (t : ℂ)) (𝓝 0) (𝓝 z₀) := by
      have h : ContinuousAt (fun t : ℝ ↦ z₀ + (t : ℂ)) 0 := by fun_prop
      simpa using h.tendsto
    have h₂ : Filter.Tendsto (fun t : ℝ ↦ z₀ - (t : ℂ)) (𝓝 0) (𝓝 z₀) := by
      have h : ContinuousAt (fun t : ℝ ↦ z₀ - (t : ℂ)) 0 := by fun_prop
      simpa using h.tendsto
    exact (h₁.eventually hopen).and (h₂.eventually hopen)
  -- `f` solves the system wherever it is defined.
  have hfd : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt f (v t (f t)) t := by
    filter_upwards [hcont] with t ht
    exact (((L.hasDerivAt_weierstrassP ht.1).comp_const_add z₀ (t : ℂ)).comp_ofReal).prodMk
      (((L.hasDerivAt_derivWeierstrassP ht.1).comp_const_add z₀ (t : ℂ)).comp_ofReal)
  -- and so does `g`.
  have hgd : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt g (v t (g t)) t := by
    filter_upwards [hcont] with t ht
    refine (((L.hasDerivAt_weierstrassP ht.2).comp_const_sub z₀ (t : ℂ)).comp_ofReal).prodMk ?_
    have hd := (((L.hasDerivAt_derivWeierstrassP ht.2).comp_const_sub z₀ (t : ℂ)).comp_ofReal).neg
    rwa [Pi.neg_def, neg_neg] at hd
  -- Both curves start at `(℘ z₀, 0)`, so they stay in the Lipschitz set near `0`.
  have hf0 : f 0 = (℘[L] z₀, (0 : ℂ)) := by simp [hf, h]
  have hg0 : g 0 = (℘[L] z₀, (0 : ℂ)) := by simp [hg, h]
  have hfS : ∀ᶠ t : ℝ in 𝓝 0, f t ∈ S :=
    hfd.self_of_nhds.continuousAt.eventually_mem (hf0 ▸ hS)
  have hgS : ∀ᶠ t : ℝ in 𝓝 0, g t ∈ S :=
    hgd.self_of_nhds.continuousAt.eventually_mem (hg0 ▸ hS)
  have key := ODE_solution_unique_of_eventually (v := v) (s := fun _ ↦ S) (K := K) (t₀ := 0)
    (f := f) (g := g) (Filter.Eventually.of_forall fun _ ↦ hK) (hfd.and hfS) (hgd.and hgS)
    (hf0.trans hg0.symm)
  filter_upwards [key] with t ht
  exact congrArg Prod.fst ht

/-- If $\wp'(z_0) = 0$ then $\wp(z_0 + z) = \wp(z_0 - z)$ whenever both sides are defined: the two
sides are analytic on the complement of the countable set $(\Lambda - z_0) \cup (z_0 - \Lambda)$,
which is connected, and they agree on a real segment through $0$. -/
lemma weierstrassP_add_eq_sub_of_derivWeierstrassP_eq_zero {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice)
    (h : ℘'[L] z₀ = 0) {z : ℂ} (hz : z₀ + z ∉ L.lattice) (hz' : z₀ - z ∉ L.lattice) :
    ℘[L] (z₀ + z) = ℘[L] (z₀ - z) := by
  set U : Set ℂ := {w | z₀ + w ∉ L.lattice ∧ z₀ - w ∉ L.lattice} with hU
  -- `U` is the complement of a countable set, hence preconnected.
  have hUeq : U = ((fun l ↦ l - z₀) '' L.lattice ∪ (fun l ↦ z₀ - l) '' L.lattice)ᶜ := by
    ext w
    simp only [hU, mem_ofPred_eq, mem_compl_iff, mem_union, mem_image, not_or, not_exists]
    constructor
    · exact fun hw ↦ ⟨fun l ⟨hl, hlw⟩ ↦ hw.1 (by rwa [show z₀ + w = l by rw [← hlw]; ring]),
        fun l ⟨hl, hlw⟩ ↦ hw.2 (by rwa [show z₀ - w = l by rw [← hlw]; ring])⟩
    · exact fun hw ↦ ⟨fun hmem ↦ hw.1 (z₀ + w) ⟨hmem, by ring⟩,
        fun hmem ↦ hw.2 (z₀ - w) ⟨hmem, by ring⟩⟩
  have hUconn : IsPreconnected U := by
    rw [hUeq]
    exact Complex.isPreconnected_compl_of_countable
      ((L.countable_lattice.image _).union (L.countable_lattice.image _))
  -- Both sides are analytic on `U`.
  have hF : AnalyticOnNhd ℂ (fun w ↦ ℘[L] (z₀ + w)) U := fun w hw ↦
    (L.analyticOnNhd_weierstrassP _ hw.1).comp (by fun_prop)
  have hG : AnalyticOnNhd ℂ (fun w ↦ ℘[L] (z₀ - w)) U := fun w hw ↦
    (L.analyticOnNhd_weierstrassP _ hw.2).comp (by fun_prop)
  -- They agree frequently near `0`, by the local symmetry along the real axis.
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), ℘[L] (z₀ + w) = ℘[L] (z₀ - w) := by
    have hT : Filter.Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with t ht using
          by simpa using (Complex.ofReal_ne_zero.mpr ht))
    exact hT.frequently
      (((L.eventually_weierstrassP_add_eq_sub hz₀ h).filter_mono nhdsWithin_le_nhds).frequently)
  have h0 : (0 : ℂ) ∈ U := by
    simp only [hU, mem_ofPred_eq, add_zero, sub_zero]
    exact ⟨hz₀, hz₀⟩
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hUconn h0 hfreq ⟨hz, hz'⟩

/-- The zeros of $\wp'$ off the lattice are half-periods: if $\wp'(z_0) = 0$ then $2 z_0$ is a
period of $\wp$, and since $\wp$ has a pole of order $2$ at $0$ it is not analytic at $2 z_0$, so
$2 z_0 \in \Lambda$. -/
lemma two_mul_mem_lattice_of_derivWeierstrassP_eq_zero {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice)
    (h : ℘'[L] z₀ = 0) : 2 * z₀ ∈ L.lattice := by
  by_contra h2
  -- If `2 z₀` is not a period, `w ↦ ℘(2 z₀ - w)` is analytic at `0`, where `℘` has a double pole.
  have hnear : {w : ℂ | 2 * z₀ - w ∉ L.lattice} ∈ 𝓝 (0 : ℂ) := by
    have hca : ContinuousAt (fun w : ℂ ↦ 2 * z₀ - w) 0 := by fun_prop
    exact hca.preimage_mem_nhds
      (by simpa using L.isClosed_lattice.isOpen_compl.mem_nhds h2)
  have hev : ℘[L] =ᶠ[𝓝[≠] (0 : ℂ)] fun w ↦ ℘[L] (2 * z₀ - w) := by
    filter_upwards [L.eventually_notMem_lattice, mem_nhdsWithin_of_mem_nhds hnear] with w hw hw2
    have hsym := L.weierstrassP_add_eq_sub_of_derivWeierstrassP_eq_zero hz₀ h
      (z := w - z₀) (by rwa [add_sub_cancel]) (by rwa [show z₀ - (w - z₀) = 2 * z₀ - w by ring])
    rwa [add_sub_cancel, show z₀ - (w - z₀) = 2 * z₀ - w by ring] at hsym
  -- Comparing orders at `0` gives `-2 ≥ 0`, a contradiction.
  have hord : meromorphicOrderAt ℘[L] 0 = -2 := L.order_weierstrassP 0 (zero_mem _)
  have hpos : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun w ↦ ℘[L] (2 * z₀ - w)) 0 := by
    refine AnalyticAt.meromorphicOrderAt_nonneg ?_
    exact (L.analyticOnNhd_weierstrassP _ (by simpa using h2)).comp (by fun_prop)
  rw [← meromorphicOrderAt_congr hev, hord] at hpos
  exact absurd hpos (by decide)

/-- **The zeros of $\wp'$ are the half-periods**: for $z \notin \Lambda$, $\wp'(z) = 0$ if and only
if $2z \in \Lambda$. -/
theorem derivWeierstrassP_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ 2 * z ∈ L.lattice :=
  ⟨L.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero hz,
    L.derivWeierstrassP_eq_zero_of_two_mul_mem⟩

end PeriodPair
