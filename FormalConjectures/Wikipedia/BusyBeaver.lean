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
module

public import FormalConjecturesUtil

/-!
# Busy Beaver

The Busy Beaver problem asks for the maximum number of steps that an n-state, 2-symbol Turing
machine can take before halting, when started on an empty tape.

*References:*

- [The Busy Beaver Challenge](https://wiki.bbchallenge.org/wiki/Main_Page)
-/

@[expose] public section

universe u v

open Turing BusyBeaver

namespace BusyBeaver

structure Candidate (n : ℕ) where
  Γ : Type
  Λ : Type
  Γ_fintype : Fintype Γ
  Γ_card : Fintype.card Γ = 2
  Γ_inhabited : Inhabited Γ
  Λ_fintype : Fintype Λ
  Λ_card : Fintype.card Λ = n
  Λ_inhabited : Inhabited Λ
  M : Machine Γ Λ
  M_isHalting : M.IsHalting

instance {n : ℕ} {M : Candidate n} : Fintype M.Γ := M.Γ_fintype
instance {n : ℕ} {M : Candidate n} : Fintype M.Λ := M.Λ_fintype
instance {n : ℕ} {M : Candidate n} : Inhabited M.Γ := M.Γ_inhabited
instance {n : ℕ} {M : Candidate n} : Inhabited M.Λ := M.Λ_inhabited

/--
`BB(n)` is the `n`-th Busy Beaver number.
*This is the maximum shifts function*, not the "number of ones function"
-/
noncomputable def BB (n : ℕ) : ℕ :=
  sSup { N | ∃ C : Candidate n, C.M.haltingNumber = N}

/--
To compute `BB n`, we need only consider machines with states and symbols indexed in `Fin`.
-/
@[category API, AMS 3]
theorem sanity_check (n : ℕ) [NeZero n] :
    BB n = sSup {N | ∃ (M : Machine (Fin 2) (Fin n)) (_ : M.IsHalting),
      M.haltingNumber = N} := by
  sorry

/-- The value of the Busy Beaver function for 1 state is 1. -/
@[category test, AMS 3]
theorem BB_1 : BB 1 = 1  := by
  have hblank : ∀ (Γ : Type) [inst : Inhabited Γ] (i : ℤ),
      (Tape.mk₁ ([] : List Γ)).nth i = (default : Γ) := by
    intro Γ inst i
    cases i with
    | ofNat k =>
      cases k with
      | zero =>
        simp [Tape.nth, Tape.mk₁, Tape.mk₂, Tape.mk', ListBlank.head_mk, List.headI]
      | succ k =>
        simp [Tape.nth, Tape.mk₁, Tape.mk₂, Tape.mk', ListBlank.nth_mk]
    | negSucc k =>
      simp [Tape.nth, Tape.mk₁, Tape.mk₂, Tape.mk', ListBlank.nth_mk]
  have hhead0 : ∀ (Γ : Type) [inst : Inhabited Γ],
      (Tape.mk₁ ([] : List Γ)).head = (default : Γ) := by
    intro Γ inst
    simpa only [Tape.nth_zero] using hblank Γ 0
  have key : ∀ (C : Candidate 1), C.M.haltingNumber ≤ (1 : ℕ∞) := by
    intro C
    have hsub : Subsingleton C.Λ := by
      obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp C.Λ_card
      exact ⟨fun a b => (hx a).trans (hx b).symm⟩
    have neverR : ∀ (w : C.Γ),
        C.M (default : C.Λ) (default : C.Γ) = some (some (default : C.Λ), ⟨w, Dir.right⟩) →
        ∀ n : ℕ, ∃ T : Tape C.Γ,
          C.M.multiStep (Machine.init []) n = some ⟨some (default : C.Λ), T⟩ ∧
          ∀ i : ℤ, (0 ≤ i ∨ i < -(n : ℤ)) → T.nth i = (default : C.Γ) := by
      intro w hM n
      induction n with
      | zero =>
        refine ⟨_, rfl, ?_⟩
        intro i _
        exact hblank C.Γ i
      | succ n ih =>
        obtain ⟨T, hT, hF⟩ := ih
        have hhead : T.head = (default : C.Γ) := hF 0 (Or.inl (le_refl 0))
        have hstep : C.M.step ⟨some (default : C.Λ), T⟩
            = some ⟨some (default : C.Λ), (T.write w).move Dir.right⟩ := by
          have hval : C.M (default : C.Λ) T.head
              = some (some (default : C.Λ), ⟨w, Dir.right⟩) := by
            rw [hhead]; exact hM
          simp only [Machine.step]
          rw [hval]
          rfl
        refine ⟨(T.write w).move Dir.right, ?_, ?_⟩
        · rw [Machine.multiStep_succ, hT, Option.bind_some]
          exact hstep
        · intro i hi
          rw [Tape.move_right_nth, Tape.write_nth]
          rw [if_neg (by omega)]
          exact hF (i + 1) (by omega)
    have neverL : ∀ (w : C.Γ),
        C.M (default : C.Λ) (default : C.Γ) = some (some (default : C.Λ), ⟨w, Dir.left⟩) →
        ∀ n : ℕ, ∃ T : Tape C.Γ,
          C.M.multiStep (Machine.init []) n = some ⟨some (default : C.Λ), T⟩ ∧
          ∀ i : ℤ, (i ≤ 0 ∨ (n : ℤ) < i) → T.nth i = (default : C.Γ) := by
      intro w hM n
      induction n with
      | zero =>
        refine ⟨_, rfl, ?_⟩
        intro i _
        exact hblank C.Γ i
      | succ n ih =>
        obtain ⟨T, hT, hF⟩ := ih
        have hhead : T.head = (default : C.Γ) := hF 0 (Or.inl (le_refl 0))
        have hstep : C.M.step ⟨some (default : C.Λ), T⟩
            = some ⟨some (default : C.Λ), (T.write w).move Dir.left⟩ := by
          have hval : C.M (default : C.Λ) T.head
              = some (some (default : C.Λ), ⟨w, Dir.left⟩) := by
            rw [hhead]; exact hM
          simp only [Machine.step]
          rw [hval]
          rfl
        refine ⟨(T.write w).move Dir.left, ?_, ?_⟩
        · rw [Machine.multiStep_succ, hT, Option.bind_some]
          exact hstep
        · intro i hi
          rw [Tape.move_left_nth, Tape.write_nth]
          rw [if_neg (by omega)]
          exact hF (i - 1) (by omega)
    have hsub' : ∀ q : C.Λ, q = (default : C.Λ) := fun q => Subsingleton.elim q _
    have h2 : C.M.multiStep (Machine.init []) 2 = none := by
      have hinit : Machine.init ([] : List C.Γ)
          = ⟨some (default : C.Λ), Tape.mk₁ ([] : List C.Γ)⟩ := rfl
      cases hdef : C.M (default : C.Λ) (default : C.Γ) with
      | none =>
        have hst : C.M.step (Machine.init ([] : List C.Γ)) = none := by
          simp only [hinit, Machine.step, hhead0 C.Γ]
          rw [hdef]
          rfl
        have h1 : C.M.multiStep (Machine.init ([] : List C.Γ)) 1 = none := by
          rw [Machine.multiStep_one, hst]
        exact Machine.multiStep_eq_none_mono h1 (by omega)
      | some hd =>
        obtain ⟨q', s⟩ := hd
        cases q' with
        | none =>
          have hst : C.M.step (Machine.init ([] : List C.Γ))
              = some ⟨none, (Tape.write s.symbol (Tape.mk₁ ([] : List C.Γ))).move s.dir⟩ := by
            simp only [hinit, Machine.step, hhead0 C.Γ]
            rw [hdef]
            rfl
          have hh : C.M.multiStep (Machine.init ([] : List C.Γ)) 2 = none := by
            have h2 := Machine.multiStep_succ C.M (Machine.init ([] : List C.Γ)) 1
            rw [Machine.multiStep_one, hst, Option.bind_some] at h2
            simpa only [Machine.step, Nat.add_one] using h2
          exact hh
        | some q'' =>
          rw [hsub' q''] at hdef
          obtain ⟨w, d⟩ := s
          exfalso
          refine (Machine.not_isHalting_iff_forall_isSome_multiStep C.M).2 ?_ C.M_isHalting
          intro n
          have hnh : ∀ m : ℕ, ∃ cfg : Cfg C.Γ C.Λ,
              C.M.multiStep (Machine.init ([] : List C.Γ)) m = some cfg := by
            intro m
            cases d with
            | right =>
              obtain ⟨T, hT, _⟩ := neverR w hdef m
              exact ⟨⟨some (default : C.Λ), T⟩, hT⟩
            | left =>
              obtain ⟨T, hT, _⟩ := neverL w hdef m
              exact ⟨⟨some (default : C.Λ), T⟩, hT⟩
          obtain ⟨cfg, hT⟩ := hnh (n + 1)
          rw [hT]
          rfl
    unfold Machine.haltingNumber
    refine sInf_le (Set.mem_ofPred_eq.mpr ⟨1, h2, rfl⟩)
  have hex : ∃ C : Candidate 1, C.M.haltingNumber = (1 : ℕ∞) := by
    let M : Machine (Fin 2) (Fin 1) := fun _ a => some (none, ⟨a, Dir.left⟩)
    have hB : M.multiStep (Machine.init ([] : List (Fin 2))) 2 = none := by rfl
    have hA : ∃ cfg : Cfg (Fin 2) (Fin 1),
        M.multiStep (Machine.init ([] : List (Fin 2))) 1 = some cfg := by
      refine ⟨⟨none, (Tape.write (default : Fin 2) (Tape.mk₁ ([] : List (Fin 2)))).move
        Dir.left⟩, ?_⟩
      rfl
    have hnum : M.haltingNumber = (1 : ℕ∞) := by
      exact Machine.haltingNumber_def M 1 hA hB
    have hhalts : M.IsHalting := by
      rw [Machine.isHalting_iff_exists_haltsAt]
      exact ⟨1, hB⟩
    refine ⟨{ Γ := Fin 2, Λ := Fin 1,
              Γ_fintype := inferInstance, Γ_card := by simp,
              Γ_inhabited := inferInstance,
              Λ_fintype := inferInstance, Λ_card := by simp,
              Λ_inhabited := inferInstance,
              M := M, M_isHalting := hhalts }, ?_⟩
    exact hnum
  have hsup : sSup { N : ℕ | ∃ C : Candidate 1, C.M.haltingNumber = ↑N } = 1 := by
    apply le_antisymm
    · refine csSup_le ⟨_, hex⟩ ?_
      rintro N ⟨C, hC⟩
      have hle : (↑N : ℕ∞) ≤ (1 : ℕ∞) := by
        rw [← hC]; exact key C
      exact WithTop.coe_le_coe.1 hle
    · refine le_csSup (s := { N : ℕ | ∃ C : Candidate 1, C.M.haltingNumber = ↑N }) ?_ ?_
      · refine ⟨1, ?_⟩
        intro N hN
        rw [Set.mem_ofPred_eq] at hN
        obtain ⟨C, hC⟩ := hN
        have hle : (↑N : ℕ∞) ≤ (1 : ℕ∞) := by
          rw [← hC]; exact key C
        exact WithTop.coe_le_coe.1 hle
      · exact Set.mem_ofPred_eq.mpr hex
  unfold BB
  exact hsup

/-- The value of the Busy Beaver function for 2 states is 6. -/
@[category textbook, AMS 3]
theorem BB_2 : BB 2 = 6 := by
  sorry

/-- The value of the Busy Beaver function for 3 states is 21. -/
@[category textbook, AMS 3]
theorem BB_3 : BB 3 = 21 := by
  sorry

/-- The value of the Busy Beaver function for 4 states is 107. -/
@[category textbook, AMS 3]
theorem BB_4 : BB 4 = 107 := by
  sorry

/-- The value of the Busy Beaver function for 5 states is 47176870. -/
@[category research solved, AMS 3]
theorem BB_5 : BB 5 = 47176870 := by
  sorry

/--
Determine the value of the Busy Beaver function at n = 6.
-/
@[category research open, AMS 3]
theorem BB_6 : BB 6 = answer(sorry) := by
  sorry

end BusyBeaver
