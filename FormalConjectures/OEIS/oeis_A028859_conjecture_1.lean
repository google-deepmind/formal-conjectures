/-
Copyright 2026 Google LLC

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

import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




/--
A028859 (OEIS): $a(n+2) = 2 \cdot a(n+1) + 2 \cdot a(n)$; $a(0) = 1$, $a(1) = 3$.
-/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 3
  | (n + 2) => 2 * a (n + 1) + 2 * a n
termination_by n

set_option linter.unusedVariables false

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
def S_pred_list (l : List ℕ) : Prop :=
  l.length > 0 ∧
  (∀ x ∈ l, x > 0) ∧
  let max_val := l.foldr max 0;
  (∀ k, 1 ≤ k ∧ k ≤ max_val → k ∈ l) ∧
  (∀ i j : Fin l.length, i.val < j.val → j.val ≠ i.val + 1 → l.get i ≥ l.get j)

def list_max (l : List ℕ) : ℕ := l.foldr max 0

def op1_uniq (l : List ℕ) : List ℕ :=
  (list_max l + 1) :: l

def op1_dup (l : List ℕ) : List ℕ :=
  list_max l :: l

def op2 (l : List ℕ) : List ℕ :=
  match l with
  | [] => []
  | h :: t => h :: (list_max l + 1) :: t

def next_state (state : List (List ℕ) × List (List ℕ)) : List (List ℕ) × List (List ℕ) :=
  let G := state.1
  let G_Y := state.2
  let new_G_Y := (G.map op1_uniq) ++ (G.map op1_dup)
  let new_G := new_G_Y ++ (G_Y.map op2)
  (new_G, new_G_Y)

def gen_states : ℕ → List (List ℕ) × List (List ℕ)
| 0 => ([[1]], [[1]])
| n + 1 => next_state (gen_states n)

def gen_G (n : ℕ) : List (List ℕ) := (gen_states n).1

lemma a_0 : a 0 = 1 := by zify[a]
lemma a_1 : a 1 = 3 := by push_cast[a]
lemma a_add_2 (n : ℕ) : a (n + 2) = 2 * a (n + 1) + 2 * a n := by delta and a
                                                                  apply WellFounded.Nat.fix_eq

lemma gen_states_length_0 : (gen_states 0).1.length = a 0 ∧ (gen_states 0).2.length = 1 := by norm_num[a, false,gen_states]
lemma gen_states_length_1 : (gen_states 1).1.length = a 1 ∧ (gen_states 1).2.length = 2 * a 0 := by push_cast[a, two_mul,gen_states]
                                                                                                    norm_num[next_state]

lemma gen_G_length (n : ℕ) : (gen_G n).length = a n := by
  delta a gen_G
  delta gen_states and
  norm_num[next_state, two_mul,add_comm]
  induction n using ↑Nat.twoStepInduction with|zero| one =>exact (.symm (by apply WellFounded.Nat.fix_eq))| more=>exact (WellFounded.Nat.fix_eq _ _ _▸by simp_all![ ← add_assoc])

lemma gen_G_all_length (n : ℕ) : ∀ l ∈ gen_G n, l.length = n + 1 := by
  norm_num[gen_G]
  induction n using@Nat.strongRec
  cases‹ℕ›
  · norm_num [gen_states]
  simp_all! (config := {singlePass := 1}) -contextual
  simp_all (config := {singlePass := 1}) -contextual [next_state]
  simp_all(config := {singlePass := 1}) -contextual [op1_uniq, or_imp, true,op1_dup, false,op2,eq_comm]
  replace : ∀M ∈(gen_states (by bound)).2, M.length =by bound+1
  · induction‹ℕ› with|zero=> decide|_=>_
    simp_all![Nat.le_succ_iff]
    simp_all![next_state,or_imp]
    use (by cases((‹∀_, _› _) :).2 rfl · with tauto)
  · use fun and=>⟨ fun and A B=>B▸congr_arg _ ((‹∀ (n : ℕ),_›:) ( _) (by constructor) and A), fun and A B=>B▸congr_arg _ ((‹∀ (n : ℕ),_›:) ( _) (by constructor) and A), (by cases. with grind)⟩

def to_seq {n : ℕ} (l : List ℕ) : Fin (n + 1) → ℕ :=
  fun i => l.getI i.val

def F_list (n : ℕ) : List (Fin (n + 1) → ℕ) :=
  (gen_G n).map to_seq

def F_set (n : ℕ) : Finset (Fin (n + 1) → ℕ) :=
  (F_list n).toFinset

lemma F_list_length (n : ℕ) : (F_list n).length = a n := by
  norm_num[a, F_list]
  delta gen_G and a
  delta gen_states and
  norm_num[next_state, two_mul,add_comm]
  induction n using ↑Nat.twoStepInduction with|zero| one=>exact (.symm (by apply WellFounded.Nat.fix_eq)) | more=>exact (WellFounded.Nat.fix_eq _ _ _▸by simp_all![←add_assoc])

def is_valid_Y (l : List ℕ) : Prop :=
  l ≠ [] ∧ l.headI = list_max l

lemma op1_uniq_inj : ∀ l₁ l₂, op1_uniq l₁ = op1_uniq l₂ → l₁ = l₂ := by delta op1_uniq
                                                                        grind
lemma op1_dup_inj : ∀ l₁ l₂, op1_dup l₁ = op1_dup l₂ → l₁ = l₂ := by delta op1_dup
                                                                     simp_all
lemma op2_inj : ∀ l₁ l₂, op2 l₁ = op2 l₂ → l₁ = l₂ := by delta op2
                                                         aesop

lemma op1_uniq_dup_disj : ∀ l₁ l₂, op1_uniq l₁ ≠ op1_dup l₂ := by delta op1_uniq Ne op1_dup
                                                                  grind
lemma op1_uniq_op2_disj : ∀ l₁ l₂, is_valid_Y l₂ → op1_uniq l₁ ≠ op2 l₂ := by delta is_valid_Y op1_uniq Ne op2
                                                                              delta list_max
                                                                              use fun and A B=>match A with | S::x=> (by cases List.cons_eq_cons.1 · with grind)
lemma op1_dup_op2_disj : ∀ l₁ l₂, is_valid_Y l₂ → op1_dup l₁ ≠ op2 l₂ := by delta op1_dup is_valid_Y Ne op2
                                                                            use fun and K V=>match K with | S::x=>mt List.cons_eq_cons.1 (by simp_all[list_max,ne_of_gt,Nat.lt_succ,·.2])

lemma G_Y_is_valid_Y (n : ℕ) : ∀ l ∈ (gen_states n).2, is_valid_Y l := by norm_num(config := {singlePass:=1})[is_valid_Y, true,gen_states]
                                                                          induction n with|zero=> decide | succ =>_
                                                                          simp_all!-contextual
                                                                          simp_all(config := {singlePass:=1})[next_state]
                                                                          norm_num[op1_uniq,op1_dup,forall_and, or_imp,eq_comm]
                                                                          norm_num+contextual[list_max,List.cons_ne_nil]

lemma nodup_op1_uniq {l : List (List ℕ)} (h : l.Nodup) : (l.map op1_uniq).Nodup := by norm_num[op1_uniq, false, l.nodup_map_iff_inj_on h]
lemma nodup_op1_dup {l : List (List ℕ)} (h : l.Nodup) : (l.map op1_dup).Nodup := by delta op1_dup
                                                                                    convert h.map ( fun and R M =>List.cons_eq_cons.mp M|>.2)
lemma nodup_op2 {l : List (List ℕ)} (h : l.Nodup) : (l.map op2).Nodup := by norm_num[op2, l.nodup_map_iff_inj_on h]
                                                                            (aesop )

lemma disjoint_op1_uniq_dup {l1 l2 : List (List ℕ)} : List.Disjoint (l1.map op1_uniq) (l2.map op1_dup) := by delta op1_uniq op1_dup List.Disjoint
                                                                                                             grind
lemma disjoint_op1_uniq_op2 {l1 l2 : List (List ℕ)} (h : ∀ l ∈ l2, is_valid_Y l) : List.Disjoint (l1.map op1_uniq) (l2.map op2) := by delta op1_uniq is_valid_Y op2 at *
                                                                                                                                      delta Ne list_max at*
                                                                                                                                      use@List.forall_mem_map.2 fun and n=>mt List.mem_map.1 fun⟨A, B, M⟩=>absurd M ((h A B).elim (by cases A with grind))
lemma disjoint_op1_dup_op2 {l1 l2 : List (List ℕ)} (h : ∀ l ∈ l2, is_valid_Y l) : List.Disjoint (l1.map op1_dup) (l2.map op2) := by delta op1_dup op2 is_valid_Y at *
                                                                                                                                    delta list_max Ne at*
                                                                                                                                    exact (List.forall_mem_map.2 fun and(a)=>mt List.mem_map.1 fun⟨A, B, M⟩=>(h A B).elim (by cases A with|nil=>nofun|cons=>cases List.cons_eq_cons.1 M with grind))

lemma nodup_append {A B : List (List ℕ)} (hA : A.Nodup) (hB : B.Nodup) (hAB : A.Disjoint B) : (A ++ B).Nodup := by use hA.append hB hAB

lemma gen_states_nodup (n : ℕ) :
  (gen_states n).1.Nodup ∧ (gen_states n).2.Nodup := by
  induction n with
  | zero =>
    norm_num [gen_states]
  | succ n ih =>
    have h1 := ih.1
    have h2 := ih.2
    simp_all!
    simp_all only [next_state]
    norm_num[op1_uniq,op1_dup,op2,List.nodup_append,List.nodup_map_iff_inj_on, *]
    simp_all(config := {singlePass:=1})[list_max, or_imp]
    use⟨⟨fun A B R L=>? _,fun A B R L=>?_⟩,fun _ _ _=>⟨fun A B true => true▸? _,fun A B true => true▸?_⟩⟩, by aesop
    · match A with | [] => (cases R with simp_all) | n::o => cases R with simp_all
    · match R with|[]=>nofun | S::x=>use fun and=>absurd (List.cons_eq_cons.1 and) (by grind)
    · match n with | 0 => aesop | 1 => aesop | 2 => aesop | n + 3 => aesop
    · match A with|[]=>nofun | S::x=>use (by cases List.cons_eq_cons.1 · with grind)

def S_pred_seq (n : ℕ) (σ : Fin (n + 1) → ℕ) : Prop :=
  n + 1 > 0 ∧
  (∀ i, σ i > 0) ∧
  let max_val := Finset.univ.sup σ;
  (∀ k, 1 ≤ k ∧ k ≤ max_val → ∃ i, σ i = k) ∧
  (∀ i j, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)

lemma S_pred_list_op1_uniq (l : List ℕ) : S_pred_list l → S_pred_list (op1_uniq l) := by delta and S_pred_list op1_uniq
                                                                                         simp_all? (config := {singlePass:=1})-contextual[list_max,Nat.succ_pos _, Fin.forall_iff_succ]
                                                                                         use fun and a s R=>by use a,fun A B=>.rec (·.eq_or_lt.imp_right (s A B ∘ A.le_of_lt_succ)) (.inr ∘s A B),fun A B=>le_add_right ↑(l.rec (nofun) (by simp_all) l[A.1] (l.getElem_mem A.2))
lemma S_pred_list_op1_dup (l : List ℕ) : S_pred_list l → S_pred_list (op1_dup l) := by delta op1_dup S_pred_list
                                                                                       simp_all? (config := {singlePass:=1})-contextual [list_max,Nat.succ_pos _, Fin.forall_iff_succ]
                                                                                       use fun and(a) R M=>⟨⟨match l with | S::x=>le_sup_left.trans_lt' (a S (by constructor)),a⟩,(.inr ∘R · ·),fun A B=>l.rec (nofun) ?_ l[A.1] (l.getElem_mem _),M⟩
                                                                                       use fun and A B=> A.forall_mem_cons.2 ⟨le_sup_left,(le_sup_of_le_right ∘B ·)⟩
lemma S_pred_list_op2 (l : List ℕ) : S_pred_list l → is_valid_Y l → S_pred_list (op2 l) := by delta is_valid_Y and S_pred_list op2
                                                                                              cases l with |nil=>nofun |cons=>_
                                                                                              simp_all? (config := {singlePass:=1})-contextual [list_max,Nat.succ_pos _, Fin.forall_iff_succ]
                                                                                              use fun and A B R L M=>(max_eq_left M).symm▸⟨⟨and, A⟩, fun and a s=>or_iff_not_imp_left.2 fun and' =>or_iff_not_imp_left.2 fun andx=>(B and a (by valid)).resolve_left and',? _,by tauto⟩
                                                                                              use fun and=>.trans (↑((‹List ↑ℕ›:).rec (nofun) (by simp_all) (‹List (@ ℕ)› :)[ and.val] (List.getElem_mem _) ) ) M

lemma gen_G_valid_both (n : ℕ) :
  (∀ l ∈ (gen_states n).1, S_pred_list l) ∧ (∀ l ∈ (gen_states n).2, S_pred_list l) := by
  induction n with
  | zero =>
    simp_all -contextual[gen_states]
    delta and S_pred_list
    exists (by constructor), (by decide), fun and=>And.elim (by decide +revert)
  | succ n ih =>
    have h1 := ih.1
    have h2 := ih.2
    have hy := G_Y_is_valid_Y n
    constructor
    · intro l hl
      -- l is in new_G
      have h_cases : l ∈ (gen_states n).1.map op1_uniq ∨ l ∈ (gen_states n).1.map op1_dup ∨ l ∈ (gen_states n).2.map op2 := by
        simp_all! (config := {singlePass := 1}) -contextual
        grind[next_state]
      rcases h_cases with h_op1u | h_op1d | h_op2
      · rcases List.mem_map.mp h_op1u with ⟨l', hl', heq⟩
        rw [←heq]
        exact S_pred_list_op1_uniq l' (h1 l' hl')
      · rcases List.mem_map.mp h_op1d with ⟨l', hl', heq⟩
        rw [←heq]
        exact S_pred_list_op1_dup l' (h1 l' hl')
      · rcases List.mem_map.mp h_op2 with ⟨l', hl', heq⟩
        rw [←heq]
        exact S_pred_list_op2 l' (h2 l' hl') (hy l' hl')
    · intro l hl
      -- l is in new_G_Y
      have h_cases : l ∈ (gen_states n).1.map op1_uniq ∨ l ∈ (gen_states n).1.map op1_dup := by
        simp_all! only [List.mem_map]
        simp_all[is_valid_Y,next_state]
      rcases h_cases with h_op1u | h_op1d
      · rcases List.mem_map.mp h_op1u with ⟨l', hl', heq⟩
        rw [←heq]
        exact S_pred_list_op1_uniq l' (h1 l' hl')
      · rcases List.mem_map.mp h_op1d with ⟨l', hl', heq⟩
        rw [←heq]
        exact S_pred_list_op1_dup l' (h1 l' hl')

lemma gen_G_valid (n : ℕ) : ∀ l ∈ (gen_states n).1, S_pred_list l := (gen_G_valid_both n).1
lemma gen_G_Y_valid (n : ℕ) : ∀ l ∈ (gen_states n).2, S_pred_list l := (gen_G_valid_both n).2

lemma to_seq_inj {n : ℕ} {l1 l2 : List ℕ} (h1 : l1.length = n + 1) (h2 : l2.length = n + 1) (h : to_seq l1 = to_seq (n:=n) l2) : l1 = l2 := by
  delta to_seq at*
  simp_all [List.getI,List.ext_get_iff,funext_iff, Fin.forall_iff]

lemma F_list_nodup (n : ℕ) : (F_list n).Nodup := by
  have h_nodup := (gen_states_nodup n).1
  have h_len := gen_G_all_length n
  unfold F_list
  have h_inj_on : ∀ (x : List ℕ), x ∈ gen_G n → ∀ (y : List ℕ), y ∈ gen_G n → to_seq x = to_seq (n:=n) y → x = y := by
    intro l1 h1 l2 h2 heq
    have hl1 := h_len l1 h1
    have hl2 := h_len l2 h2
    exact to_seq_inj hl1 hl2 heq
  exact List.Nodup.map_on h_inj_on h_nodup

lemma F_set_card (n : ℕ) : (F_set n).card = a n := by
  have h_nodup : (F_list n).Nodup := F_list_nodup n
  have h1 : (F_set n).card = (F_list n).length := by
    exact List.toFinset_card_of_nodup h_nodup
  have h2 : (F_list n).length = a n := F_list_length n
  rw [h1, h2]

lemma to_seq_preserves_valid (n : ℕ) (l : List ℕ) (h_len : l.length = n + 1) (h_valid : S_pred_list l) : S_pred_seq n (to_seq l) := by
  borelize ℂ
  simp_all[S_pred_list,S_pred_seq,to_seq]
  delta to_seq
  refine h_len▸h_valid.imp (by norm_num[List.getI,.]) (.imp ( fun and A B x =>(List.get_of_mem (and A B (x.trans ( Finset.sup_le fun and i=>?_)))).imp (by norm_num[List.getI])) ? _)
  · norm_num[List.getI]
  · exact (l.rec (nofun) (by aesop) (l.getI _) (by norm_num[List.getI]:l.getI and ∈l))

lemma F_subset_S (n : ℕ) (σ : Fin (n + 1) → ℕ) : σ ∈ F_set n → S_pred_seq n σ := by
  intro h
  have h_in_F_list : σ ∈ F_list n := by
    exact List.mem_toFinset.mp h
  rcases List.mem_map.mp h_in_F_list with ⟨l, hl, heq⟩
  have h_valid := gen_G_valid n l hl
  have h_len := gen_G_all_length n l hl
  have h_seq_valid := to_seq_preserves_valid n l h_len h_valid
  rw [←heq]
  exact h_seq_valid

lemma decompose_op1_uniq (l : List ℕ) (h_len : l.length ≥ 2) (h_valid : S_pred_list l) (hy : is_valid_Y l) (hm : l.headI > list_max l.tail) : ∃ t, S_pred_list t ∧ l = op1_uniq t := by delta is_valid_Y list_max and S_pred_list op1_uniq at*
                                                                                                                                                                                        replace:l.tail.foldr max 0+1=l.headI:=le_antisymm hm ((l.get_of_mem (h_valid.2.2.1 _ ⟨le_add_self,by linarith⟩)).elim fun and true => true.subst ? _)
                                                                                                                                                                                        · refine match l with | S::x=> ⟨x,⟨Nat.le_of_lt_succ h_len,(h_valid.2.1 · ∘x.mem_cons_of_mem _),?_⟩,this▸rfl⟩
                                                                                                                                                                                          use fun and p=>(x.mem_cons.mp (h_valid.2.2.left and (hy.right▸p.imp_right hm.le.trans'))).resolve_left (p.2.trans_lt (↑hm)).ne, (h_valid.right.right.right ·.succ ·.succ |>.comp (Nat.succ_lt_succ) ·<| · ∘? _)
                                                                                                                                                                                          norm_num
                                                                                                                                                                                        · cases@l with|nil=>tauto|cons=>_
                                                                                                                                                                                          use match and with |⟨00, _⟩=>by constructor | ⟨a+1, _⟩=>true.not_lt.elim (Nat.lt_succ.2 ((‹List ↑ℕ›:).rec (nofun) ?_ ((List.get _) _) ((List.get_mem _) ⟨a,Nat.le_of_lt_succ (by assumption)⟩)))
                                                                                                                                                                                          exact fun and R L=> R.forall_mem_cons.mpr ⟨le_sup_left, (le_sup_of_le_right ∘ L ·)⟩
lemma decompose_op1_dup (l : List ℕ) (h_len : l.length ≥ 2) (h_valid : S_pred_list l) (hy : is_valid_Y l) (hm : l.headI = list_max l.tail) : ∃ t, S_pred_list t ∧ l = op1_dup t := by delta and S_pred_list is_valid_Y op1_dup at *
                                                                                                                                                                                      refine match l with | S::x=>⟨x,⟨Nat.sub_pos_of_lt h_len,(h_valid.2.1 · ∘x.mem_cons_of_mem _),?_⟩,hm▸rfl⟩
                                                                                                                                                                                      norm_num[Max.max, false, Fin.forall_iff_succ] at *
                                                                                                                                                                                      use fun and A B=>(h_valid.2.1 and A (.inr B)).elim (.▸hm▸? _) ↑id,(h_valid.2.2 ·.succ ·.succ|>.comp (Nat.succ_lt_succ) ·<|. ∘Nat.succ_inj.1)
                                                                                                                                                                                      delta list_max
                                                                                                                                                                                      refine x.rec (nofun) ?_ (by valid : 1 ≤x.length)
                                                                                                                                                                                      use fun and A B n=>match A with|[]=>by norm_num | S::A=>List.mem_cons.2 ((max_choice _ _).imp_right ↑(·.symm.subst (B A.length.succ_pos)))
lemma decompose_op2 (l : List ℕ) (h_len : l.length ≥ 2) (h_valid : S_pred_list l) (hy : ¬ is_valid_Y l) : ∃ t, S_pred_list t ∧ is_valid_Y t ∧ l = op2 t := by delta op2 S_pred_list is_valid_Y at*
                                                                                                                                                              cases l with|nil=>contradiction|cons=>_
                                                                                                                                                              revert‹ℕ›‹List _›
                                                                                                                                                              simp_all? (config := {singlePass:=1}) -contextual [list_max, Fin.forall_iff_succ]
                                                                                                                                                              use fun and A B a s R M K V=>match A with | S::A=> if I: S≤ and then(? _)else(? _)
                                                                                                                                                              · norm_num[I, A.mem_iff_getElem, Fin.forall_iff_succ] at M V
                                                                                                                                                                rcases V.elim I.not_gt (not_lt.mpr (A.rec (by·bound) (by simp_all[ Fin.forall_iff_succ]) M))
                                                                                                                                                              use and::A
                                                                                                                                                              simp_all[ Fin.forall_iff_succ]
                                                                                                                                                              replace K: A.foldr Max.max 0≤and:= A.rec (by(bound)) (? _) M
                                                                                                                                                              · use fun and A B C=>max_le (C ⟨0,by bound⟩) (B (C ·.succ))
                                                                                                                                                              use(R · ·|>.comp (.imp_right .inr) ·|>.imp_right (·.resolve_left (by valid))), K,symm ((congr_arg (.+1)<|max_eq_left K).trans (by_contra fun and' =>absurd (R (and+1)) ?_))
                                                                                                                                                              norm_num[*, and.succ_le, A.mem_iff_get,ne_of_lt,Nat.lt_succ]

lemma valid_list_in_gen_both (n : ℕ) :
  (∀ l : List ℕ, l.length = n + 1 → S_pred_list l → l ∈ (gen_states n).1) ∧
  (∀ l : List ℕ, l.length = n + 1 → S_pred_list l → is_valid_Y l → l ∈ (gen_states n).2) := by
  induction n with
  | zero =>
    simp_all!
    repeat use fun and n=>match and with|[n]=> (by cases. with grind)
  | succ n ih =>
    have h1 := ih.1
    have h2 := ih.2
    constructor
    · intro l h_len h_valid
      have h_cases : is_valid_Y l ∨ ¬ is_valid_Y l := Classical.em _
      rcases h_cases with hy | hy
      · have h_cases2 : l.headI > list_max l.tail ∨ l.headI = list_max l.tail := by delta list_max S_pred_list is_valid_Y at *
                                                                                    cases l with |nil=>contradiction|cons=>exact (lt_or_eq_of_le')<|hy.2▸le_sup_right
        rcases h_cases2 with hm | hm
        · have hl_len : l.length ≥ 2 := by omega
          rcases decompose_op1_uniq l hl_len h_valid hy hm with ⟨t, ht_valid, heq⟩
          simp_all!
          simp_all[op1_uniq,next_state]
        · have hl_len : l.length ≥ 2 := by omega
          rcases decompose_op1_dup l hl_len h_valid hy hm with ⟨t, ht_valid, heq⟩
          simp_all[op1_dup,gen_states]
          simp_all[next_state]
          delta is_valid_Y op1_uniq op1_dup op2 list_max S_pred_list at*
          exact (.inr (.inl ⟨ _,h1 t h_len (by tauto), rfl⟩))
      · have hl_len : l.length ≥ 2 := by omega
        rcases decompose_op2 l hl_len h_valid hy with ⟨t, ht_valid, ht_y, heq⟩
        -- t is in gen_states n .2
        simp_all!
        simp_all[is_valid_Y,op2,next_state]
        exact (.inr (.inr ⟨ _,by cases t with|nil=>tauto|cons=>exact (ht_y).elim (h2 (_) (Nat.succ_injective h_len) (ht_valid)), rfl⟩))
    · intro l h_len h_valid hy
      have h_cases : l.headI > list_max l.tail ∨ l.headI = list_max l.tail := by delta list_max S_pred_list is_valid_Y at *
                                                                                 cases l with |nil=>contradiction|cons=>exact (lt_or_eq_of_le')<|hy.2▸le_sup_right
      rcases h_cases with hm | hm
      · have hl_len : l.length ≥ 2 := by omega
        rcases decompose_op1_uniq l hl_len h_valid hy hm with ⟨t, ht_valid, heq⟩
        -- t is in gen_states n .1
        simp_all![op1_uniq]
        delta list_max is_valid_Y next_state S_pred_list at*
        exact (List.mem_append_left _) ((List.mem_map.2 ⟨ _,h1 t h_len (by tauto), rfl⟩))
      · have hl_len : l.length ≥ 2 := by omega
        rcases decompose_op1_dup l hl_len h_valid hy hm with ⟨t, ht_valid, heq⟩
        -- t is in gen_states n .1
        simp_all only[is_valid_Y, true,gen_states,op1_dup]
        simp_all[next_state,show t≠[] from(by cases.▸h_len)]
        delta list_max op1_uniq op1_dup S_pred_list at*
        exact (.inr ⟨ _,by apply_rules, rfl⟩)

lemma valid_list_in_gen_G (n : ℕ) (l : List ℕ) (h_len : l.length = n + 1) (h_valid : S_pred_list l) : l ∈ gen_G n := by
  exact (valid_list_in_gen_both n).1 l h_len h_valid

lemma seq_to_list_valid (n : ℕ) (σ : Fin (n + 1) → ℕ) (h_valid : S_pred_seq n σ) : ∃ l, l.length = n + 1 ∧ S_pred_list l ∧ to_seq l = σ := by
  push_cast[funext_iff,to_seq,S_pred_seq,S_pred_list]at*
  use(List.finRange (n + 1)).map σ,by norm_num, ⟨by norm_num[*],List.forall_mem_map.2 (by bound),(h_valid.2.2.1 ·|>.comp (.imp_right ? _) ·|>.elim (by bound)),?_⟩
  · norm_num[List.getI]
    use fun and=>List.getElem?_eq_getElem (and.2.trans_eq (List.length_finRange).symm)▸by norm_num
  · exact (id)
  · simp_all

lemma S_subset_F (n : ℕ) (σ : Fin (n + 1) → ℕ) : S_pred_seq n σ → σ ∈ F_set n := by
  intro h
  rcases seq_to_list_valid n σ h with ⟨l, h_len, h_valid, heq⟩
  have h_in_gen_G := valid_list_in_gen_G n l h_len h_valid
  have h_in_F_list : σ ∈ F_list n := by
    rw [←heq]
    exact List.mem_map.mpr ⟨l, h_in_gen_G, rfl⟩
  exact List.mem_toFinset.mpr h_in_F_list
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) :
    let L := n + 1
    let Sequence := Fin L → ℕ
    let S : Set Sequence :=
      {σ : Sequence |
        L > 0 ∧
          (∀ i : Fin L, σ i > 0) ∧
            let max_val := Finset.sup Finset.univ σ
            (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin L, σ i = k) ∧ (∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)}
    ∃ (F : Finset Sequence), F.toSet = S ∧ F.card = a n := by
  -- EVOLVE-BLOCK-START
  intro L Sequence S
  use F_set n
  have h_set : (F_set n).toSet = S := by
    ext σ
    constructor
    · intro h
      have h1 := F_subset_S n σ h
      simp_all(config := {singlePass:=1})[Sequence, S, L, F_set,S_pred_seq]
    · intro h
      have h1 := S_subset_F n σ h
      try assumption
  have h_card : (F_set n).card = a n := by
    exact F_set_card n
  exact ⟨h_set, h_card⟩
  -- EVOLVE-BLOCK-END
