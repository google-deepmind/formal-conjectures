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

public import FormalConjecturesForMathlib.Computability.Frege

/-!
# Frege and Extended Frege proofs

Proofs are chronological lists of formulas, ending in their conclusion.
Extended Frege additionally permits a fresh variable to abbreviate a formula.
The variable may occur neither in its definition, earlier lines, nor the final
conclusion. Soundness extends a valuation at each such line.

References: Cook–Reckhow (1979), Definition 4.1 and Proposition 4.2, p.44,
https://www.karlin.mff.cuni.cz/~krajicek/cr79.pdf;
Krajíček, *The Cook-Reckhow definition*, §2,
https://arxiv.org/abs/1909.03691.

The explicit checker and soundness theorem do not assert a formal TM simulation
or a completeness proof for the fixed Frege calculus.
-/

@[expose] public section

namespace PropositionalProof

open Formula

/-- Recognize the fixed expansion of an equivalence between a variable and a formula. -/
def extensionData : Formula → Option (ℕ × Formula)
  | .neg (.imp (.imp (.var v) d) (.neg (.imp d' (.var v')))) =>
    if v = v' ∧ d = d' then some (v, d) else none
  | _ => none

theorem extensionData_sound {p : Formula} {v : ℕ} {d : Formula}
    (h : extensionData p = some (v, d)) : p = Formula.iff (.var v) d := by
  unfold extensionData at h
  split at h
  next w a b w' =>
    split at h
    next he =>
      rcases he with ⟨rfl, rfl⟩
      cases h
      rfl
    next => simp at h
  next => simp at h

@[simp]
theorem extensionData_iff (v : ℕ) (d : Formula) :
    extensionData (Formula.iff (.var v) d) = some (v, d) := by
  simp [Formula.iff, Formula.conj, extensionData]

def extensionStep (goal : Formula) (earlier : List Formula) (p : Formula) : Bool :=
  match extensionData p with
  | none => false
  | some (v, d) =>
    decide (v ∉ d.support ∧ v ∉ goal.support ∧ ∀ q ∈ earlier, v ∉ q.support)

theorem extensionStep_spec {goal p : Formula} {earlier : List Formula}
    (h : extensionStep goal earlier p = true) :
    ∃ v d, p = Formula.iff (.var v) d ∧ v ∉ d.support ∧
      v ∉ goal.support ∧ ∀ q ∈ earlier, v ∉ q.support := by
  unfold extensionStep at h
  split at h
  next => simp at h
  next v d he =>
    exact ⟨v, d, extensionData_sound he, by simpa using h⟩

/-- A fresh extension preserves earlier lines and the conclusion, and makes its
defining line true. Extension lines are not themselves tautologies. -/
theorem extensionStep_sound {goal p : Formula} {earlier : List Formula}
    (h : extensionStep goal earlier p = true) (a : ℕ → Bool)
    (ha : ∀ q ∈ earlier, q.eval a = true) :
    ∃ b : ℕ → Bool, goal.eval b = goal.eval a ∧ p.eval b = true ∧
      ∀ q ∈ earlier, q.eval b = true := by
  obtain ⟨v, d, rfl, hd, hg, he⟩ := extensionStep_spec h
  refine ⟨Function.update a v (d.eval a), eval_update _ hg, ?_, ?_⟩
  · simp [eval_iff, eval, eval_update _ hd]
  · intro q hq
    rw [eval_update _ (he q hq)]
    exact ha q hq

/-- The earlier context is stored in reverse order, so its head is the latest line. -/
def checkFrom (extended : Bool) (goal : Formula) (earlier : List Formula) :
    List Formula → Bool
  | [] => earlier.head? == some goal
  | p :: rest =>
    (Frege.step earlier p || (extended && extensionStep goal earlier p)) &&
      checkFrom extended goal (p :: earlier) rest

theorem checkFrom_sound {extended : Bool} {goal : Formula}
    {earlier proof : List Formula} (h : checkFrom extended goal earlier proof = true)
    (a : ℕ → Bool) (ha : ∀ q ∈ earlier, q.eval a = true) : goal.eval a = true := by
  induction proof generalizing earlier a with
  | nil =>
    have he : earlier.head? = some goal := by simpa [checkFrom] using h
    exact ha goal (List.mem_of_head? he)
  | cons p rest ih =>
    have hr :
        (Frege.step earlier p = true ∨
          (extended = true ∧ extensionStep goal earlier p = true)) ∧
        checkFrom extended goal (p :: earlier) rest = true := by
      simpa only [checkFrom, Bool.and_eq_true, Bool.or_eq_true] using h
    rcases hr with ⟨hs, ht⟩
    rcases hs with hs | ⟨_, hs⟩
    · apply ih ht a
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Frege.step_sound hs a ha
      · exact ha q hq
    · obtain ⟨b, hg, hp, hb⟩ := extensionStep_sound hs a ha
      rw [← hg]
      apply ih ht b
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact hb q hq

/-- Frege proof checking, with the extension rule disabled. -/
def fregeProof (goal : Formula) (proof : List Formula) : Bool :=
  checkFrom false goal [] proof

/-- Extended Frege proof checking, with all extension freshness conditions enforced. -/
def extendedFregeProof (goal : Formula) (proof : List Formula) : Bool :=
  checkFrom true goal [] proof

theorem fregeProof_sound {goal : Formula} {proof : List Formula}
    (h : fregeProof goal proof = true) : goal.Tautology := by
  rw [tautology_iff]
  intro a
  exact checkFrom_sound h a (by simp)

theorem extendedFregeProof_sound {goal : Formula} {proof : List Formula}
    (h : extendedFregeProof goal proof = true) : goal.Tautology := by
  rw [tautology_iff]
  intro a
  exact checkFrom_sound h a (by simp)

theorem checkFrom_mono {goal : Formula} {earlier proof : List Formula}
    (h : checkFrom false goal earlier proof = true) :
    checkFrom true goal earlier proof = true := by
  induction proof generalizing earlier with
  | nil => exact h
  | cons p rest ih =>
    have he : Frege.step earlier p = true ∧
        checkFrom false goal (p :: earlier) rest = true := by
      simpa [checkFrom] using h
    simp [checkFrom, he.1, ih he.2]

theorem fregeProof_implies_extendedFregeProof {goal : Formula} {proof : List Formula}
    (h : fregeProof goal proof = true) : extendedFregeProof goal proof = true :=
  checkFrom_mono h

/-- Total bit length, not merely the number of lines or distinct subformulas. -/
def proofSize (proof : List Formula) : ℕ := (BitstringEncoding.bitEncode proof).length

@[simp]
theorem proofSize_nil : proofSize [] = 0 := rfl

@[simp]
theorem proofSize_cons (p : Formula) (proof : List Formula) :
    proofSize (p :: proof) = 2 * p.size + 1 + proofSize proof := by
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode p) ++
    BitstringEncoding.bitEncode proof).length = _
  rw [List.length_append, BitstringEncoding.length_delimit]
  rfl

theorem size_le_proofSize {p : Formula} {proof : List Formula} (h : p ∈ proof) :
    p.size ≤ proofSize proof := by
  induction proof with
  | nil => simp at h
  | cons q rest ih =>
    rw [proofSize_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have hr := ih h
      omega

/-- Every tautology has a proof bounded by one global polynomial in its encoded size. -/
def PolynomiallyBounded (checker : Formula → List Formula → Bool) : Prop :=
  ∃ C k : ℕ, ∀ p : Formula, p.Tautology →
    ∃ proof : List Formula, checker p proof = true ∧ proofSize proof ≤ C * (p.size + 1) ^ k

/-- A simulation only bounds the lengths of replacement proofs; it need not find them. -/
def ProofSimulates (target source : Formula → List Formula → Bool) : Prop :=
  ∃ C k : ℕ, ∀ (p : Formula) (proof : List Formula), source p proof = true →
    ∃ replacement : List Formula, target p replacement = true ∧
      proofSize replacement ≤ C * (proofSize proof + 1) ^ k

end PropositionalProof
