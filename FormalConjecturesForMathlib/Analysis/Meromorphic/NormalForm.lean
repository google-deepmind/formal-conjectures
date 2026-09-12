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

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

open Filter Set
open scoped Topology

/-- The identity theorem for meromorphic functions on `ℂ` in normal form: two of them that agree
near a point are equal. -/
theorem MeromorphicNFOn.eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f g : ℂ → E} (hf : MeromorphicNFOn f univ) (hg : MeromorphicNFOn g univ)
    {z₀ : ℂ} (hfg : f =ᶠ[𝓝 z₀] g) : f = g := by
  set V : Set ℂ := {z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z}
  have hVmem (z : ℂ) : V ∈ 𝓝[≠] z := by
    have h₁ := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp
      hf.meromorphicOn.analyticAt_mem_codiscreteWithin z (mem_univ z)
    have h₂ := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp
      hg.meromorphicOn.analyticAt_mem_codiscreteWithin z (mem_univ z)
    simp only [compl_univ, union_empty] at h₁ h₂
    exact inter_mem h₁ h₂
  have hVpre : IsPreconnected V := by
    have hc : ({z : ℂ | AnalyticAt ℂ f z}ᶜ ∪ {z : ℂ | AnalyticAt ℂ g z}ᶜ).Countable := by
      simpa using hf.meromorphicOn.countable_compl_analyticAt_inter.union
        hg.meromorphicOn.countable_compl_analyticAt_inter
    have hconn := hc.isConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex])
    rw [compl_union, compl_compl, compl_compl] at hconn
    exact hconn.isPreconnected
  obtain ⟨U, hUsub, hUopen, hz₀U⟩ := mem_nhds_iff.mp hfg
  obtain ⟨w, hwV, hwU⟩ : (V ∩ U).Nonempty :=
    nonempty_of_mem (inter_mem (hVmem z₀) (mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hz₀U)))
  have hfA : AnalyticOnNhd ℂ f V := fun _ hz ↦ hz.1
  have hgA : AnalyticOnNhd ℂ g V := fun _ hz ↦ hz.2
  have hEq : EqOn f g V := hfA.eqOn_of_preconnected_of_eventuallyEq hgA hVpre hwV
    (eventually_of_mem (hUopen.mem_nhds hwU) fun _ hz ↦ hUsub hz)
  funext x
  have hx : f =ᶠ[𝓝[≠] x] g := by filter_upwards [hVmem x] with z hz using hEq hz
  exact (((hf (mem_univ x)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hg (mem_univ x))).mp hx).eq_of_nhds
