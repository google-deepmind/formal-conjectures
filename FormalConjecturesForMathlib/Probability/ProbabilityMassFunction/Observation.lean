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

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Updating a probability mass function after an observation

`PMF.observe` updates a hidden-state distribution after a random observation. A fixed fallback
state specifies its value when the observation has probability zero. `PMF.observeUpdate` also
applies a stochastic state update, and uses its designated final state directly at null observations.
The reconstruction lemmas cover that case. They support the behavioral realization of finite-memory
strategies.

This is discrete Bayes conditioning, using `PMF.normalize` and `PMF.filter`.
-/

@[expose] public section

namespace PMF

open scoped ENNReal

noncomputable section

variable {M A M' : Type*}

/-- The probability of observing `a` when a hidden state has distribution `prior`. -/
def observationMass (prior : PMF M) (act : M → PMF A) (a : A) : ℝ≥0∞ :=
  prior.bind act a

/-- Bayes updating, with a designated hidden state used at zero-probability observations. -/
def observe (prior : PMF M) (act : M → PMF A) (a : A) (fallback : M) : PMF M := by
  classical
  exact if h : observationMass prior act a = 0 then pure fallback
    else normalize (fun m ↦ prior m * act m a) h ((prior.bind act).apply_ne_top a)

@[simp]
theorem observe_of_mass_eq_zero (prior : PMF M) (act : M → PMF A) (a : A)
    (fallback : M) (h : observationMass prior act a = 0) :
    observe prior act a fallback = pure fallback := by
  simp [observe, h]

theorem observe_apply_of_mass_ne_zero (prior : PMF M) (act : M → PMF A) (a : A)
    (fallback m : M) (h : observationMass prior act a ≠ 0) :
    observe prior act a fallback m = prior m * act m a * (observationMass prior act a)⁻¹ := by
  simp only [observationMass, bind_apply] at h
  simp [observe, observationMass, h]
  rfl

/-- The Bayes reconstruction identity remains valid for impossible observations. -/
theorem observationMass_mul_observe (prior : PMF M) (act : M → PMF A) (a : A)
    (fallback m : M) :
    observationMass prior act a * observe prior act a fallback m = prior m * act m a := by
  classical
  by_cases h : observationMass prior act a = 0
  · have hm : prior m * act m a = 0 := by
      have ht : (∑' x, prior x * act x a) = 0 := h
      exact ENNReal.tsum_eq_zero.mp ht m
    simp [h, hm]
  · rw [observe_apply_of_mass_ne_zero prior act a fallback m h]
    calc
      _ = (prior m * act m a) *
          (observationMass prior act a * (observationMass prior act a)⁻¹) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel h ((prior.bind act).apply_ne_top a), mul_one]

/-- Filtering followed by a stochastic state update reconstructs the original joint mass. -/
theorem observationMass_mul_observe_bind (prior : PMF M) (act : M → PMF A) (a : A)
    (fallback : M) (update : M → PMF M') (m' : M') :
    observationMass prior act a * (observe prior act a fallback).bind update m' =
      ∑' m, prior m * act m a * update m m' := by
  rw [bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun m ↦ ?_
  rw [← mul_assoc, observationMass_mul_observe]

/-- Observe and update the hidden state, using a designated final state at null observations. -/
def observeUpdate (prior : PMF M) (act : M → PMF A) (a : A) (fallback : M')
    (update : M → PMF M') : PMF M' := by
  classical
  exact if h : observationMass prior act a = 0 then pure fallback
    else (normalize (fun m ↦ prior m * act m a) h
      ((prior.bind act).apply_ne_top a)).bind update

@[simp]
theorem observeUpdate_of_mass_eq_zero (prior : PMF M) (act : M → PMF A) (a : A)
    (fallback : M') (update : M → PMF M') (h : observationMass prior act a = 0) :
    observeUpdate prior act a fallback update = pure fallback := by
  simp [observeUpdate, h]

/-- At a possible observation, `observeUpdate` is the usual posterior followed by the update. -/
theorem observeUpdate_of_mass_ne_zero (prior : PMF M) (act : M → PMF A) (a : A)
    (fallback : M') (update : M → PMF M') (hiddenFallback : M)
    (h : observationMass prior act a ≠ 0) :
    observeUpdate prior act a fallback update = (observe prior act a hiddenFallback).bind update := by
  simp only [observeUpdate, observe, dif_neg h]

/-- The observe-update reconstruction identity includes zero-probability observations. -/
theorem observationMass_mul_observeUpdate (prior : PMF M) (act : M → PMF A) (a : A)
    (fallback : M') (update : M → PMF M') (m' : M') :
    observationMass prior act a * observeUpdate prior act a fallback update m' =
      ∑' m, prior m * act m a * update m m' := by
  classical
  by_cases h : observationMass prior act a = 0
  · have hz (m : M) : prior m * act m a = 0 :=
      ENNReal.tsum_eq_zero.mp h m
    simp [h, hz]
  · obtain ⟨m, _⟩ := prior.support_nonempty
    rw [observeUpdate_of_mass_ne_zero prior act a fallback update m h]
    exact observationMass_mul_observe_bind prior act a m update m'

/-- The joint law of the hidden state and its random observation. -/
def observationJoint (prior : PMF M) (act : M → PMF A) : PMF (M × A) :=
  prior.bind fun m ↦ (act m).map fun a ↦ (m, a)

@[simp]
theorem observationJoint_apply (prior : PMF M) (act : M → PMF A) (m : M) (a : A) :
    observationJoint prior act (m, a) = prior m * act m a := by
  classical
  simp only [observationJoint, bind_apply, map_apply, Prod.mk.injEq]
  rw [tsum_eq_single m]
  · simp
  · intro b hb
    simp [Ne.symm hb]

/-- A nonzero observation mass supplies the support witness needed by `PMF.filter`. -/
theorem exists_observationJoint_support (prior : PMF M) (act : M → PMF A) (a : A)
    (h : observationMass prior act a ≠ 0) :
    ∃ x ∈ {x : M × A | x.2 = a}, x ∈ (observationJoint prior act).support := by
  classical
  have he : ∃ m, prior m * act m a ≠ 0 := by
    by_contra! he
    exact h (ENNReal.tsum_eq_zero.mpr he)
  obtain ⟨m, hm⟩ := he
  exact ⟨(m, a), rfl, by simpa [PMF.mem_support_iff] using hm⟩

/-- At a possible observation, updating equals conditioning the joint law and keeping the state. -/
theorem observe_eq_filter_observationJoint (prior : PMF M) (act : M → PMF A) (a : A)
    (fallback : M) (h : observationMass prior act a ≠ 0) :
    observe prior act a fallback =
      ((observationJoint prior act).filter {x : M × A | x.2 = a}
        (exists_observationJoint_support prior act a h)).map Prod.fst := by
  classical
  ext m
  rw [observe_apply_of_mass_ne_zero prior act a fallback m h, map_apply]
  simp only [filter_apply, ENNReal.tsum_prod', Set.indicator_apply, Set.mem_ofPred_eq,
    observationJoint_apply]
  rw [tsum_eq_single m]
  · simp only [if_true]
    rw [ENNReal.tsum_mul_right, tsum_ite_eq]
    simp only [tsum_ite_eq]
    rfl
  · intro b hb
    simp [Ne.symm hb]

/-- An action independent of the hidden state leaves its prior unchanged when it is possible. -/
theorem observe_const (prior : PMF M) (act : PMF A) (a : A) (fallback : M)
    (h : act a ≠ 0) : observe prior (fun _ ↦ act) a fallback = prior := by
  have hm : observationMass prior (fun _ ↦ act) a = act a := by
    simp [observationMass]
  ext m
  rw [observe_apply_of_mass_ne_zero prior (fun _ ↦ act) a fallback m (hm ▸ h), hm,
    ENNReal.mul_inv_cancel_right h (act.apply_ne_top a)]

/-- With one possible hidden state, even a null observation retains that unique state. -/
theorem observe_subsingleton [Subsingleton M] (prior : PMF M) (act : M → PMF A)
    (a : A) (fallback : M) : observe prior act a fallback = pure fallback := by
  classical
  have hp (p : PMF M) : p = pure fallback := by
    ext m
    have hs : (∑' x : M, p x) = p fallback := by
      rw [tsum_eq_single fallback]
      intro x hx
      exact (hx (Subsingleton.elim x fallback)).elim
    rw [p.tsum_coe] at hs
    simpa [Subsingleton.elim m fallback] using hs.symm
  exact hp _

end

end PMF
