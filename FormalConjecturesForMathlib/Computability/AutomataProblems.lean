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

public import FormalConjecturesForMathlib.Computability.StringProblems
public import Mathlib.Computability.DFA

/-!
# Encoded deterministic automata decision problems

Reference: Garey and Johnson, *Computers and Intractability* (1979),
AL6, p. 266, and AL8, p. 267.
https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf

Transition tables denote actual Mathlib DFAs. A shortest-word argument makes
intersection nonemptiness decidable without imposing an arbitrary word cutoff.
Inference searches all K-state transition functions and accepting-state sets.
These finite searches make no polynomial-time claim.
-/

@[expose] public section

namespace Computability.AutomataProblems

open StringProblems

/-- Transition rows, initial state, and one accepting flag per state. -/
abbrev Code := List (List ℕ) × ℕ × List Bool

/-- A total transition table over the specified alphabet, with a valid initial state. -/
def ValidCode (m : ℕ) (c : Code) : Prop :=
  c.2.1 < c.1.length ∧ c.2.2.length = c.1.length ∧
    ∀ q : Fin c.1.length, c.1[q].length = m ∧ ∀ r ∈ c.1[q], r < c.1.length

instance (m : ℕ) (c : Code) : Decidable (ValidCode m c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _ : Fin c.1.length, _))

/-- Validated tables have no missing transitions and require no default state. -/
def toDFA (m : ℕ) (c : Code) (h : ValidCode m c) : DFA (Fin m) (Fin c.1.length) where
  step q a := ⟨c.1[q][a.val]'(by rw [(h.2.2 q).1]; exact a.isLt),
    (h.2.2 q).2 _ (List.getElem_mem _)⟩
  start := ⟨c.2.1, h.1⟩
  accept := {q | c.2.2[q.val]'(by rw [h.2.1]; exact q.isLt) = true}

instance (m : ℕ) (c : Code) (h : ValidCode m c) (w : List (Fin m)) :
    Decidable (w ∈ (toDFA m c h).accepts) :=
  inferInstanceAs (Decidable (_ = true))

/-- The simultaneous product of an input-sized family of DFAs. -/
def intersectionDFA {α ι : Type} {σ : ι → Type} (M : (i : ι) → DFA α (σ i)) :
    DFA α ((i : ι) → σ i) where
  step q a i := (M i).step (q i) a
  start i := (M i).start
  accept := {q | ∀ i, q i ∈ (M i).accept}

theorem intersectionDFA_evalFrom {α ι : Type} {σ : ι → Type}
    (M : (i : ι) → DFA α (σ i)) (q : (i : ι) → σ i) (w : List α) (i : ι) :
    (intersectionDFA M).evalFrom q w i = (M i).evalFrom (q i) w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => exact ih _

theorem intersectionDFA_accepts {α ι : Type} {σ : ι → Type}
    (M : (i : ι) → DFA α (σ i)) (w : List α) :
    w ∈ (intersectionDFA M).accepts ↔ ∀ i, w ∈ (M i).accepts := by
  change (∀ i, (intersectionDFA M).evalFrom _ w i ∈ (M i).accept) ↔ _
  simp only [intersectionDFA_evalFrom]
  rfl

/-- Removing a repeated-state loop yields an accepted word shorter than the state count. -/
theorem exists_short_word {α σ : Type} [Fintype σ] (M : DFA α σ)
    {w : List α} (hw : w ∈ M.accepts) :
    ∃ v, v.length < Fintype.card σ ∧ v ∈ M.accepts := by
  have aux : ∀ n, ∀ u : List α, u.length = n → u ∈ M.accepts →
      ∃ v, v.length < Fintype.card σ ∧ v ∈ M.accepts := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hu hacc
      by_cases hshort : u.length < Fintype.card σ
      · exact ⟨u, hshort, hacc⟩
      obtain ⟨q, a, b, c, heq, _, hb, ha, _, hc⟩ :=
        M.evalFrom_split (s := M.start) (Nat.le_of_not_gt hshort) rfl
      have hlen : (a ++ c).length < n := by
        have hbpos := List.length_pos_iff.mpr hb
        rw [heq] at hu
        simp only [List.length_append] at *
        omega
      apply ih _ hlen (a ++ c) rfl
      change M.evalFrom M.start (a ++ c) ∈ M.accept
      rw [M.evalFrom_of_append, ha, hc]
      exact hacc
  exact aux w.length w rfl hw

theorem boundedWord_accepts_iff {α σ : Type} [Fintype σ] (M : DFA α σ) :
    BoundedWord (Fintype.card σ) (fun w ↦ w ∈ M.accepts) ↔ ∃ w, w ∈ M.accepts := by
  rw [boundedWord_iff]
  constructor
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hlen, hv⟩ := exists_short_word M hw
    exact ⟨v, Nat.le_of_lt hlen, hv⟩

/-- Common alphabet size and an arbitrary-length list of encoded automata. -/
abbrev IntersectionInput := ℕ × List Code

def AllValid (x : IntersectionInput) : Prop :=
  ∀ i : Fin x.2.length, ValidCode x.1 x.2[i]

instance (x : IntersectionInput) : Decidable (AllValid x) :=
  inferInstanceAs (Decidable (∀ _ : Fin x.2.length, _))

/-- AL6: some word is accepted by every input automaton. The product-state bound
can be exponential in the number of input automata. Malformed inputs are rejected. -/
def DFAIntersection (x : IntersectionInput) : Prop :=
  if h : AllValid x then
    BoundedWord (Fintype.card ((i : Fin x.2.length) → Fin x.2[i].1.length))
      (fun w : List (Fin x.1) ↦ ∀ i : Fin x.2.length, w ∈ (toDFA x.1 x.2[i] (h i)).accepts)
  else False

instance (x : IntersectionInput) : Decidable (DFAIntersection x) := by
  unfold DFAIntersection
  split_ifs with h
  · letI : DecidablePred (fun w : List (Fin x.1) ↦
        ∀ i : Fin x.2.length, w ∈ (toDFA x.1 x.2[i] (h i)).accepts) :=
      fun _ ↦ inferInstanceAs (Decidable (∀ _ : Fin x.2.length, _ = true))
    infer_instance
  · infer_instance

/-- The finite search expresses unrestricted common-word existence. -/
theorem dfaIntersection_iff (x : IntersectionInput) (h : AllValid x) :
    DFAIntersection x ↔ ∃ w : List (Fin x.1),
      ∀ i : Fin x.2.length, w ∈ (toDFA x.1 x.2[i] (h i)).accepts := by
  simp only [DFAIntersection, dif_pos h]
  simp_rw [← intersectionDFA_accepts]
  exact boundedWord_accepts_iff _

/-- Every K-state transition function, initial state, and accepting-state subset. -/
abbrev Witness (m K : ℕ) := (Fin K → Fin m → Fin K) × Fin K × (Fin K → Bool)

def Witness.toDFA {m K : ℕ} (c : Witness m K) : DFA (Fin m) (Fin K) where
  step := c.1
  start := c.2.1
  accept := {q | c.2.2 q = true}

instance {m K : ℕ} (c : Witness m K) (w : List (Fin m)) :
    Decidable (w ∈ c.toDFA.accepts) :=
  inferInstanceAs (Decidable (_ = true))

/-- Finite Boolean accepting flags represent every actual DFA on the given state type. -/
theorem Witness.toDFA_surjective (m K : ℕ) :
    Function.Surjective (@Witness.toDFA m K) := by
  classical
  intro M
  refine ⟨(M.step, M.start, fun q ↦ decide (q ∈ M.accept)), ?_⟩
  cases M
  simp only [Witness.toDFA, decide_eq_true_eq, Set.ofPred_mem_eq]

/-- Alphabet size, positive samples, negative samples, and state count. -/
abbrev InferenceInput := ℕ × List (List ℕ) × List (List ℕ) × ℕ

def ValidSamples (x : InferenceInput) : Prop :=
  StringsIn x.1 x.2.1 ∧ StringsIn x.1 x.2.2.1

instance (x : InferenceInput) : Decidable (ValidSamples x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Agreement on the given samples only; other words remain unconstrained. -/
def Consistent (x : InferenceInput) (h : ValidSamples x)
    (M : DFA (Fin x.1) (Fin x.2.2.2)) : Prop :=
  (∀ i : Fin x.2.1.length,
    typedWord x.2.1[i] (h.1 _ (List.getElem_mem _)) ∈ M.accepts) ∧
  (∀ i : Fin x.2.2.1.length,
    typedWord x.2.2.1[i] (h.2 _ (List.getElem_mem _)) ∉ M.accepts)

instance (x : InferenceInput) (h : ValidSamples x) (c : Witness x.1 x.2.2.2) :
    Decidable (Consistent x h c.toDFA) :=
  inferInstanceAs (Decidable ((∀ _ : Fin x.2.1.length, _) ∧
    (∀ _ : Fin x.2.2.1.length, _)))

/-- AL8: a positive K-state DFA consistent with the labeled examples.
Unreachable states are permitted. Contradictory labels cannot be satisfied. -/
def InferredDFA (x : InferenceInput) : Prop :=
  if h : ValidSamples x then
    0 < x.2.2.2 ∧ ∃ c : Witness x.1 x.2.2.2, Consistent x h c.toDFA
  else False

instance (x : InferenceInput) : Decidable (InferredDFA x) :=
  inferInstanceAs (Decidable (if _h : ValidSamples x then _ else False))

theorem inferredDFA_iff (x : InferenceInput) (h : ValidSamples x) :
    InferredDFA x ↔ 0 < x.2.2.2 ∧
      ∃ M : DFA (Fin x.1) (Fin x.2.2.2), Consistent x h M := by
  simp only [InferredDFA, dif_pos h]
  constructor
  · rintro ⟨hK, c, hc⟩
    exact ⟨hK, c.toDFA, hc⟩
  · rintro ⟨hK, M, hM⟩
    obtain ⟨c, rfl⟩ := Witness.toDFA_surjective _ _ M
    exact ⟨hK, c, hM⟩

end Computability.AutomataProblems
