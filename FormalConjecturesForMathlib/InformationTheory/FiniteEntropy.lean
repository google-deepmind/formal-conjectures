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

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.FunProp

/-!
# Shannon entropy of finite-valued random variables

This file defines Shannon entropy and mutual information, in bits, for finite-valued random
variables.

For a probability measure `μ` and a function `U` with measurable fibers, write
`q_U(a) = μ.real (U ⁻¹' {a})` for the probability that `U = a`. For a probability `q`,
`Real.negMulLog q` is `-q ln q` when `q > 0` and `0` when `q = 0`, so

`H(U) = (∑ a, Real.negMulLog (q_U a)) / Real.log 2 = -∑ a, q_U(a) log₂ q_U(a)`,

with the convention `0 log₂ 0 = 0`; dividing by `Real.log 2` converts nats to bits. Mutual
information is `I(U; V) = H(U) + H(V) - H(U, V)`.

Measurable fibers are automatic when `U` is measurable and its finite target has measurable
singletons, in particular for finite discrete targets. The definitions are total expressions for
arbitrary measures and functions; without normalization and measurable fibers they need not have
their usual probabilistic interpretation.

The main results are invariance under measurable pushforward and the formula for the mutual
information of the coordinate projections of a finite joint law.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace InformationTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Shannon entropy, in bits, of a finite-valued random variable.

For a probability measure `μ`, this is the usual Shannon entropy when every fiber
`U ⁻¹' {a}` is measurable. In particular, this holds when `U` is measurable and its target
has measurable singletons.

Zero-probability values contribute zero. The expression is also defined without these
hypotheses, but then need not have a probabilistic interpretation.
-/
noncomputable def shannonEntropyBits {α : Type*} [Fintype α]
    (μ : Measure Ω) (U : Ω → α) : ℝ :=
  (∑ a, Real.negMulLog (μ.real (U ⁻¹' {a}))) / Real.log 2

/-- Mutual information, in bits, of two finite-valued random variables, defined by
`I(U; V) = H(U) + H(V) - H(U, V)`.

For a probability measure `μ`, this is the usual mutual information when the fibers of
both `U` and `V` are measurable. In particular, this holds for measurable functions into
finite targets with measurable singletons.

The expression is also defined without these hypotheses, but then need not have a
probabilistic interpretation.
-/
noncomputable def mutualInformationBits {α : Type*} {β : Type*}
    [Fintype α] [Fintype β] (μ : Measure Ω) (U : Ω → α) (V : Ω → β) : ℝ :=
  shannonEntropyBits μ U + shannonEntropyBits μ V -
    shannonEntropyBits μ (fun ω => (U ω, V ω))

section Map

variable {Ω' : Type*} {α : Type*} {β : Type*}
    [MeasurableSpace Ω']
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Entropy commutes with measurable pushforward of the sample-space measure.
No normalization assumption on the measure is required. -/
theorem shannonEntropyBits_map (μ : Measure Ω) {T : Ω → Ω'}
    (hT : Measurable T) {U : Ω' → α} (hU : Measurable U) :
    shannonEntropyBits (μ.map T) U = shannonEntropyBits μ (U ∘ T) := by
  unfold shannonEntropyBits
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change ((μ.map T) (U ⁻¹' {a})).toReal =
    (μ ((U ∘ T) ⁻¹' {a})).toReal
  rw [Measure.map_apply hT (hU (measurableSet_singleton a))]
  rfl

/-- Mutual information commutes with measurable pushforward of the sample-space measure.
No normalization assumption on the measure is required. -/
theorem mutualInformationBits_map (μ : Measure Ω) {T : Ω → Ω'}
    (hT : Measurable T) {U : Ω' → α} {V : Ω' → β}
    (hU : Measurable U) (hV : Measurable V) :
    mutualInformationBits (μ.map T) U V =
      mutualInformationBits μ (U ∘ T) (V ∘ T) := by
  have hUV : Measurable (fun ω => (U ω, V ω)) := by fun_prop
  unfold mutualInformationBits
  rw [shannonEntropyBits_map μ hT hU, shannonEntropyBits_map μ hT hV,
    shannonEntropyBits_map μ hT hUV]
  rfl

end Map

/-- The mutual information of the coordinate projections, written using the singleton masses of
a finite measure on a finite product. -/
theorem mutualInformationBits_fst_snd {α : Type*} {β : Type*}
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (ν : Measure (α × β)) [IsFiniteMeasure ν] :
    mutualInformationBits ν Prod.fst Prod.snd =
      (∑ a, Real.negMulLog (∑ b, ν.real {(a, b)})) / Real.log 2 +
      (∑ b, Real.negMulLog (∑ a, ν.real {(a, b)})) / Real.log 2 -
      (∑ ab : α × β, Real.negMulLog (ν.real {ab})) / Real.log 2 := by
  classical
  have hsum (s : Set (α × β)) :
      ν.real s = ∑ w, if w ∈ s then ν.real {w} else 0 := by
    simpa [Finset.sum_filter] using
      (sum_measureReal_singleton (μ := ν) (Finset.univ.filter (fun w => w ∈ s))).symm
  have hfst (a : α) :
      ν.real (Prod.fst ⁻¹' {a}) = ∑ b, ν.real {(a, b)} := by
    rw [hsum]
    simp only [Fintype.sum_prod_type, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp)]
    simp
  have hsnd (b : β) :
      ν.real (Prod.snd ⁻¹' {b}) = ∑ a, ν.real {(a, b)} := by
    rw [hsum]
    simp [Fintype.sum_prod_type]
  simp [mutualInformationBits, shannonEntropyBits, hfst, hsnd]

end InformationTheory
