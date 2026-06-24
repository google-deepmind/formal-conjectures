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




open List Nat Function Set

/--
A300997: $a(n)$ is the number of steps needed to reach a stable configuration in the 1D cellular automaton initialized with one cell with mass $n$ and based on the rule "each cell gives half of its mass, rounded down, to its right neighbor".
The stable configuration is $n$ cells with mass 1.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2

  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

  let ca_step (config : List ℕ) : List ℕ :=
    let base_masses := config.map half_ceil ++ [0]
    let received_masses := 0 :: config.map half_floor

    let next_config_long := List.zipWith Nat.add base_masses received_masses

    trim_trailing_zeros next_config_long

  if n = 0 then
    0
  else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1

    -- State after t steps, computed by folding ca_step t times using foldl over a range.
    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config

    -- The set of time steps k at which the configuration is stable.
    let stable_steps : Set ℕ := {k | S k = target_config}

    -- a(n) is the smallest k in this set, defined by the set infimum (sInf).
    sInf stable_steps

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
def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2

def trim_trailing_zeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

def ca_step_list (config : List ℕ) : List ℕ :=
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trim_trailing_zeros next_config_long

def initial_config_list (n : ℕ) : List ℕ := [n]
def target_config_list (n : ℕ) : List ℕ := List.replicate n 1

def S_list (n t : ℕ) : List ℕ :=
  (List.range t).foldl (fun acc _ => ca_step_list acc) (initial_config_list n)

def ca_step_fun (f : ℕ → ℕ) : ℕ → ℕ :=
  fun i => half_ceil (f i) + if i = 0 then 0 else half_floor (f (i - 1))

def F (n t : ℕ) : ℕ → ℕ :=
  match t with
  | 0 => fun i => if i = 0 then n else 0
  | t' + 1 => ca_step_fun (F n t')

lemma a_eq_sInf (n : ℕ) (hn : 1 ≤ n) : a n = sInf {k | S_list n k = target_config_list n} := by
  show (star _) = sInf {s |_=(id _)}
  norm_num[instDecidableEqNat, S_list,mt hn.trans_eq]
  norm_num[ca_step_list,List.foldl_const,mt hn.trans_eq, true,Nat.decEq]
  cases n with tauto

def TargetF (n : ℕ) : ℕ → ℕ :=
  fun i => if i < n then 1 else 0

def list_to_fun (l : List ℕ) : ℕ → ℕ := fun i => l.getD i 0

lemma list_to_fun_initial (n : ℕ) : list_to_fun (initial_config_list n) = F n 0 := by
  delta F list_to_fun
  exact (funext (by cases. with constructor))

lemma list_to_fun_target (n : ℕ) : list_to_fun (target_config_list n) = TargetF n := by
  delta list_to_fun TargetF
  use funext fun and=>show(List.getD (id _) _ _) = _ by aesop

lemma trim_trailing_zeros_getD (l : List ℕ) (i : ℕ) :
    (trim_trailing_zeros l).getD i 0 = l.getD i 0 := by
  norm_num[trim_trailing_zeros]
  induction l using List.reverseRecOn generalizing i with| nil=>rfl| append_singleton=>_
  simp_all-contextual[List.getElem?_append, false,List.dropWhile_cons]
  split
  · exact (em _).elim (if_pos ·▸by simp_all only) (if_neg ·▸.trans (by apply_rules) (by simp_all))
  · if R:i<List.length (by valid) then cases i with simp_all[R.trans']else cases Nat.exists_eq_add_of_le (not_lt.1 R) with cases‹ℕ› with aesop

lemma getD_zipWith_add (l1 l2 : List ℕ) (h : l1.length = l2.length) (i : ℕ) :
    (List.zipWith Nat.add l1 l2).getD i 0 = l1.getD i 0 + l2.getD i 0 := by
  induction @em (@l2.length>i) with simp_all

lemma getD_append_zero (l : List ℕ) (i : ℕ) :
    (l ++ [0]).getD i 0 = l.getD i 0 := by
  rcases lt_or_ge i l.length
  · rwa[ l.getD_append]
  · cases (by assumption:).eq_or_lt with ·simp_all [Nat.succ_le]

lemma my_getD_cons_zero (l : List ℕ) (i : ℕ) :
    (0 :: l).getD i 0 = if i = 0 then 0 else l.getD (i - 1) 0 := by
  cases i with constructor

lemma getD_map_half_ceil (l : List ℕ) (i : ℕ) :
    (l.map half_ceil).getD i 0 = half_ceil (l.getD i 0) := by
  refine if a :i<l.length then ((by simp_all ) )else by simp_all [half_ceil]

lemma getD_map_half_floor (l : List ℕ) (i : ℕ) :
    (l.map half_floor).getD i 0 = half_floor (l.getD i 0) := by
  induction lt_or_ge i l.length with·norm_num[half_floor, true, *]

lemma list_to_fun_ca_step (l : List ℕ) : list_to_fun (ca_step_list l) = ca_step_fun (list_to_fun l) := by
  funext i
  unfold list_to_fun ca_step_list
  rw [trim_trailing_zeros_getD]
  have hlen : (l.map half_ceil ++ [0]).length = (0 :: l.map half_floor).length := by
    simp
  rw [getD_zipWith_add _ _ hlen]
  rw [getD_append_zero, my_getD_cons_zero]
  rw [getD_map_half_ceil, getD_map_half_floor]
  unfold ca_step_fun
  rfl

lemma S_list_zero (n : ℕ) : S_list n 0 = initial_config_list n := by
  simp_all[ S_list]

lemma S_list_succ (n t : ℕ) : S_list n (t + 1) = ca_step_list (S_list n t) := by
  delta S_list ca_step_list
  rw[List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma list_to_fun_S_list (n t : ℕ) : list_to_fun (S_list n t) = F n t := by
  induction t with
  | zero =>
    rw [S_list_zero]
    exact list_to_fun_initial n
  | succ t ih =>
    rw [S_list_succ]
    rw [list_to_fun_ca_step]
    rw [ih]
    rfl

def P (n t : ℕ) : ℕ :=
  match t with
  | 0 => 0
  | t' + 1 => P n t' + (F n t' (P n t') % 2)

def DiffByOneF (f1 f2 : ℕ → ℕ) (p : ℕ) : Prop :=
  ∀ i, f2 i = f1 i + if i = p then 1 else 0

lemma ca_step_fun_DiffByOneF (f1 f2 : ℕ → ℕ) (p : ℕ) (h : DiffByOneF f1 f2 p) :
    DiffByOneF (ca_step_fun f1) (ca_step_fun f2) (p + (f1 p % 2)) := by
  delta ca_step_fun DiffByOneF at*
  norm_num[half_ceil,half_floor,h,add_comm p]
  use fun and=>match and with|0=> (by cases(f1 p).mod_two_eq_zero_or_one with cases p with norm_num[*,ne_of_lt,Nat.add_mod,Nat.add_div]) | S+1=>S.succ_sub_one.symm▸by grind

lemma F_DiffByOneF (n t : ℕ) :
    DiffByOneF (F n t) (F (n + 1) t) (P n t) := by
  delta P tsub_zero DiffByOneF
  norm_num only [ F]
  delta F
  norm_num1
  delta ca_step_fun
  push_cast [half_ceil, true,half_floor]
  use t.rec (by cases. with rfl ) fun and A B=>by grind

lemma ca_step_fun_TargetF (n : ℕ) (hn : 1 ≤ n) :
    ca_step_fun (TargetF n) = TargetF n := by
  push_cast [TargetF,ca_step_fun, Eq.comm, false,funext_iff]
  use (by cases em<|.<n with cases em (by valid-1<n) with norm_num[*,half_ceil,half_floor])

lemma F_n_plus_1_eq (n t : ℕ) : F (n + 1) t = fun i => F n t i + if i = P n t then 1 else 0 := by
  funext i
  exact F_DiffByOneF n t i

lemma F_zero_and_P_le (n : ℕ) :
    (∀ t i, n ≤ i → F n t i = 0) ∧ (∀ t, P n t ≤ n) := by
  induction n with
  | zero =>
    have hz : ∀ t i, 0 ≤ i → F 0 t i = 0 := by
      intro t
      induction t with
      | zero =>
        intro i hi
        dsimp [F]
        split_ifs <;> omega
      | succ t ih =>
        intro i hi
        dsimp [F, ca_step_fun, half_ceil, half_floor]
        have h1 : F 0 t i = 0 := ih i hi
        have h2 : F 0 t (i - 1) = 0 := ih (i - 1) (by omega)
        rw [h1, h2]
        split_ifs <;> rfl
    constructor
    · exact hz
    · intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        dsimp [P]
        have h1 : F 0 t (P 0 t) = 0 := hz t (P 0 t) (by omega)
        rw [h1]
        omega
  | succ n ih =>
    have hn : ∀ t i, n + 1 ≤ i → F (n + 1) t i = 0 := by
      intro t i hi
      have h1 : F (n + 1) t i = F n t i + if i = P n t then 1 else 0 := congrFun (F_n_plus_1_eq n t) i
      rw [h1]
      have h2 : F n t i = 0 := ih.1 t i (by omega)
      rw [h2]
      have h3 : P n t ≤ n := ih.2 t
      have h4 : i ≠ P n t := by omega
      rw [if_neg h4]
    constructor
    · exact hn
    · intro t
      induction t with
      | zero =>
        dsimp [P]
        omega
      | succ t ih_t =>
        dsimp [P]
        have h_mod : F (n + 1) t (P (n + 1) t) % 2 ≤ 1 := by omega
        by_cases h : P (n + 1) t < n + 1
        · omega
        · have h_eq : P (n + 1) t = n + 1 := by omega
          have h_val : F (n + 1) t (n + 1) = 0 := hn t (n + 1) (by omega)
          rw [h_eq, h_val]

lemma F_zero_of_ge (n t i : ℕ) (hi : n ≤ i) : F n t i = 0 :=
  (F_zero_and_P_le n).1 t i hi

lemma P_le_n (n t : ℕ) : P n t ≤ n :=
  (F_zero_and_P_le n).2 t

lemma list_eq_of_fun_eq (l1 l2 : List ℕ) (h1 : l1.getLast? ≠ some 0) (h2 : l2.getLast? ≠ some 0)
    (h_fun : list_to_fun l1 = list_to_fun l2) : l1 = l2 := by
  delta Ne list_to_fun at*
  refine l1.ext_get (by_contra fun and=>absurd (congrFun h_fun (l1.length - 1)) (absurd (congrFun h_fun<|l2.length - 1) ∘by cases l1 with cases l2 with grind) ) fun and i=>?_
  exact (by simp_all ∘congr_arg (@ · and)) h_fun

lemma S_list_no_trailing_zeros (n t : ℕ) (hn : 1 ≤ n) : (S_list n t).getLast? ≠ some 0 := by
  delta S_list And Ne
  norm_num [ca_step_list, false,List.foldl_const]
  delta half_ceil trim_trailing_zeros half_floor
  show(( _)^[t] (id _) :List ℕ).getLast?≠_
  use t.rec (by cases hn with (nofun)) fun and J=>Function.iterate_succ_apply' _ _ _▸?_
  simp_all -contextual
  cases h:_^[_] ( _) using List.reverseRecOn with| nil=>hint| append_singleton=>_
  simp_all-contextual [List.getLast?_append,List.zipWith_append]
  clear! n t and
  rw [←List.ofFn_get (.reverse _),]
  simp_all[List.getElem_append]
  cases em (by valid/2=0) with simp_all[show (by valid+1)/2≠00by valid]

lemma target_config_no_trailing_zeros (n : ℕ) (hn : 1 ≤ n) : (target_config_list n).getLast? ≠ some 0 := by
  show(List.getLast? (id _)≠ _)
  norm_num [List.getLast?_replicate]

lemma F_eq_TargetF_iff_S_list_eq (n t : ℕ) (hn : 1 ≤ n) :
    F n t = TargetF n ↔ S_list n t = target_config_list n := by
  constructor
  · intro h
    apply list_eq_of_fun_eq (S_list n t) (target_config_list n)
    · exact S_list_no_trailing_zeros n t hn
    · exact target_config_no_trailing_zeros n hn
    · have h_fun1 := list_to_fun_S_list n t
      have h_fun2 := list_to_fun_target n
      rw [h_fun1, h_fun2]
      exact h
  · intro h
    have h_fun1 := list_to_fun_S_list n t
    have h_fun2 := list_to_fun_target n
    rw [← h_fun1, ← h_fun2]
    rw [h]

lemma a_is_stable_from_exists (n : ℕ) (hn : 1 ≤ n) (h_exists : ∃ t, F n t = TargetF n) : F n (a n) = TargetF n := by
  have h_eq1 := a_eq_sInf n hn
  rw [h_eq1]
  rw [F_eq_TargetF_iff_S_list_eq n _ hn]
  have hs : {k | S_list n k = target_config_list n}.Nonempty := by
    rcases h_exists with ⟨t, ht⟩
    use t
    exact (F_eq_TargetF_iff_S_list_eq n t hn).mp ht
  exact Nat.sInf_mem hs

lemma a_min (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (h : F n t = TargetF n) : a n ≤ t := by
  have h_eq1 := a_eq_sInf n hn
  rw [h_eq1]
  apply Nat.sInf_le
  dsimp
  have h_fun := list_to_fun_S_list n t
  rw [h] at h_fun
  have h_target := list_to_fun_target n
  rw [← h_target] at h_fun
  apply list_eq_of_fun_eq (S_list n t) (target_config_list n)
  · exact S_list_no_trailing_zeros n t hn
  · exact target_config_no_trailing_zeros n hn
  · exact h_fun

lemma P_succ (n t : ℕ) : P n (t + 1) = P n t + (F n t (P n t) % 2) := by
  rfl

lemma P_moves_when_stable (n : ℕ) (t : ℕ) (hF : F n t = TargetF n) (hp : P n t < n) :
    P n (t + 1) = P n t + 1 := by
  delta TargetF P at*
  push_cast[eq_self, *]

lemma F_stable_forward (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (hF : F n t = TargetF n) :
    F n (t + 1) = TargetF n := by
  have h_step : F n (t + 1) = ca_step_fun (F n t) := rfl
  rw [h_step, hF]
  exact ca_step_fun_TargetF n hn

lemma F_stable_add (n : ℕ) (hn : 1 ≤ n) (t k : ℕ) (hF : F n t = TargetF n) :
    F n (t + k) = TargetF n := by
  delta F TargetF at *
  delta ca_step_fun at*
  simp_all(config := {singlePass:=1}) -contextual[half_ceil,half_floor]
  use k.rec hF fun and J=>funext fun and=>show _/2+_ = _ from J.symm▸by grind

lemma P_add_stable (n : ℕ) (hn : 1 ≤ n) (t k : ℕ) (hF : F n t = TargetF n) (hp : P n t + k ≤ n) :
    P n (t + k) = P n t + k := by
  refine k.rec (by subsingleton) ( fun and R M =>.trans (by rw [t.add_succ, P]) ? _) hp
  simp_all[TargetF,Nat.le_of_lt M,←add_assoc,funext_iff]
  simp_all [le_of_lt M]
  replace hF : ∀x≤and, F n (t+x) (P n t+x) % 2 =1
  · use Nat.rec (by simp_all[M.trans_le']) fun and a s=>.trans (by rw [t.add_succ, P n t|>.add_succ, F]) ?_
    simp_all![and.le_of_lt s]
    simp_all[ca_step_fun, add_assoc]
    replace hF : ∀ R M,M<n →F n (t+R) M=1
    · use Nat.rec (hF ·▸if_pos ·) fun and _ _ _=>?_
      simp_all![←add_assoc]
      delta ca_step_fun
      norm_num[*, M.pos,half_ceil,half_floor, (by valid:).trans_le']
    · norm_num[*, M.trans_le',half_ceil, and.succ_le,half_floor,s.le]
  · repeat tauto

lemma target_n_plus_1_eq (n : ℕ) :
    (fun i => TargetF n i + if i = n then 1 else 0) = TargetF (n + 1) := by
  push_cast[TargetF,eq_self,eq_comm, true,funext_iff]
  grind

lemma F_n_plus_1_at_D (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (hF : F n t = TargetF n) (hp : P n t ≤ n) :
    F (n + 1) (t + (n - P n t)) = TargetF (n + 1) := by
  have hF_add : F n (t + (n - P n t)) = TargetF n := F_stable_add n hn t (n - P n t) hF
  have hP_add : P n (t + (n - P n t)) = n := by
    have h1 := P_add_stable n hn t (n - P n t) hF (by omega)
    omega
  have h_eq : F (n + 1) (t + (n - P n t)) = fun i => F n (t + (n - P n t)) i + if i = P n (t + (n - P n t)) then 1 else 0 := F_n_plus_1_eq n (t + (n - P n t))
  rw [hF_add, hP_add] at h_eq
  rw [h_eq]
  exact target_n_plus_1_eq n

lemma stable_at_some_time (n : ℕ) (hn : 1 ≤ n) : ∃ t, F n t = TargetF n := by
  induction' n, hn using Nat.le_induction with k hk ih
  · use 0
    funext i
    dsimp [F, TargetF]
    split_ifs <;> omega
  · rcases ih with ⟨t_k, ht_k⟩
    use t_k + (k - P k t_k)
    apply F_n_plus_1_at_D k hk t_k ht_k
    exact P_le_n k t_k

lemma a_is_stable (n : ℕ) (hn : 1 ≤ n) : F n (a n) = TargetF n := by
  exact a_is_stable_from_exists n hn (stable_at_some_time n hn)

lemma not_stable_before_D (n : ℕ) (hn : 1 ≤ n) (t k : ℕ) (hF : F n t = TargetF n)
    (hp : P n t ≤ n) (hk : k < n - P n t) : F (n + 1) (t + k) ≠ TargetF (n + 1) := by
  intro h_contra
  have h_val := congrFun h_contra n
  have hF_add : F n (t + k) = TargetF n := F_stable_add n hn t k hF
  have hP_add : P n (t + k) = P n t + k := by
    have h1 := P_add_stable n hn t k hF (by omega)
    exact h1
  have h_eq : F (n + 1) (t + k) n = F n (t + k) n + if n = P n (t + k) then 1 else 0 := by
    have h_f := F_n_plus_1_eq n (t + k)
    exact congrFun h_f n
  rw [h_val] at h_eq
  rw [hF_add, hP_add] at h_eq
  have h_target_n : TargetF n n = 0 := by
    dsimp [TargetF]
    exact if_neg (by omega)
  have h_target_n1 : TargetF (n + 1) n = 1 := by
    dsimp [TargetF]
    exact if_pos (by omega)
  rw [h_target_n, h_target_n1] at h_eq
  have h_if : (if n = P n t + k then 1 else 0) = 0 := by
    apply if_neg
    omega
  rw [h_if] at h_eq
  omega

lemma not_stable_before_a (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (ht : t < a n) : F (n + 1) t ≠ TargetF (n + 1) := by
  intro h_contra
  have h_val : F (n + 1) t n = TargetF (n + 1) n := congrFun h_contra n
  have h_eq : F (n + 1) t n = F n t n + if n = P n t then 1 else 0 := congrFun (F_n_plus_1_eq n t) n
  have h_target : TargetF (n + 1) n = 1 := by
    dsimp [TargetF]
    exact if_pos (by omega)
  rw [h_val, h_target] at h_eq
  have h_zero : F n t n = 0 := F_zero_of_ge n t n (by omega)
  rw [h_zero] at h_eq
  have h_p : P n t ≤ n := P_le_n n t
  by_cases h_pn : P n t = n
  · have h_fun : F n t = TargetF n := by
      funext i
      have h_i : F (n + 1) t i = TargetF (n + 1) i := congrFun h_contra i
      have h_i2 : F (n + 1) t i = F n t i + if i = P n t then 1 else 0 := congrFun (F_n_plus_1_eq n t) i
      rw [h_i, h_pn] at h_i2
      dsimp [TargetF] at h_i2 ⊢
      by_cases h1 : i < n
      · have h2 : i < n + 1 := by omega
        have h3 : i ≠ n := by omega
        rw [if_pos h2, if_neg h3] at h_i2
        rw [if_pos h1]
        omega
      · have h2 : ¬(i < n) := h1
        rw [if_neg h2]
        by_cases h3 : i = n
        · rw [h3] at h_i2 ⊢
          have h4 : n < n + 1 := by omega
          rw [if_pos h4, if_pos rfl] at h_i2
          omega
        · have h4 : ¬(i < n + 1) := by omega
          rw [if_neg h4, if_neg h3] at h_i2
          omega
    have h_le := a_min n hn t h_fun
    omega
  · have h_neq : n ≠ P n t := by omega
    rw [if_neg h_neq] at h_eq
    omega

lemma not_stable_before_a_plus_D (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (ht : t < a n + (n - P n (a n))) (hp : P n (a n) ≤ n) : F (n + 1) t ≠ TargetF (n + 1) := by
  have h_cases : t < a n ∨ a n ≤ t := by omega
  rcases h_cases with h_lt | h_ge
  · exact not_stable_before_a n hn t h_lt
  · have h_k : ∃ k, t = a n + k ∧ k < n - P n (a n) := ⟨t - a n, by omega, by omega⟩
    rcases h_k with ⟨k, hk_eq, hk_lt⟩
    rw [hk_eq]
    exact not_stable_before_D n hn (a n) k (a_is_stable n hn) hp hk_lt

lemma coupling_diff (n : ℕ) (hn : 1 ≤ n) (hp : P n (a n) ≤ n) : a (n + 1) = a n + (n - P n (a n)) := by
  have h1 : F (n + 1) (a n + (n - P n (a n))) = TargetF (n + 1) :=
    F_n_plus_1_at_D n hn (a n) (a_is_stable n hn) hp
  have h2 : a (n + 1) ≤ a n + (n - P n (a n)) :=
    a_min (n + 1) (by omega) (a n + (n - P n (a n))) h1
  have h_contra : ¬ (a (n + 1) < a n + (n - P n (a n))) := by
    intro h_lt
    have h_stable : F (n + 1) (a (n + 1)) = TargetF (n + 1) := a_is_stable (n + 1) (by omega)
    have h_not := not_stable_before_a_plus_D n hn (a (n + 1)) h_lt hp
    exact h_not h_stable
  omega

lemma tail_preserved (f : ℕ → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (h1 : f (n - 2) = 1) (h2 : f (n - 1) = 1) (h3 : f n = 0) :
    ca_step_fun f (n - 1) = 1 ∧ ca_step_fun f n = 0 := by
  dsimp [ca_step_fun, half_ceil, half_floor]
  have eq1 : n - 1 - 1 = n - 2 := by omega
  have eq2 : n - 1 ≠ 0 := by omega
  have eq3 : n ≠ 0 := by omega
  constructor
  · rw [h2, if_neg eq2, eq1, h1]
  · rw [h3, if_neg eq3, h2]



lemma F_no_internal_zeros (n t i : ℕ) (h : F n t i = 0) : F n t (i + 1) = 0 := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    dsimp [F, ca_step_fun] at h ⊢
    have h1 : half_ceil (F n t i) = 0 := by omega
    have h2 : F n t i = 0 := by
      dsimp [half_ceil] at h1
      omega
    have h3 : F n t (i + 1) = 0 := ih i h2
    rw [h3, h2]
    rfl

lemma F_sum_step (n t : ℕ) (K : ℕ) (hk : ∀ i ≥ K, F n t i = 0) :
    ∑ i ∈ Finset.range (K + 1), F n (t + 1) i = ∑ i ∈ Finset.range K, F n t i := by
  dsimp [F, ca_step_fun]
  have h1 : (∑ i ∈ Finset.range (K + 1), (half_ceil (F n t i) + if i = 0 then 0 else half_floor (F n t (i - 1)))) =
            (∑ i ∈ Finset.range (K + 1), half_ceil (F n t i)) + ∑ i ∈ Finset.range (K + 1), (if i = 0 then 0 else half_floor (F n t (i - 1))) := by
    exact Finset.sum_add_distrib
  rw [h1]
  have h2 : (∑ i ∈ Finset.range (K + 1), (if i = 0 then 0 else half_floor (F n t (i - 1)))) = ∑ i ∈ Finset.range K, half_floor (F n t i) := by
    rw [Finset.sum_range_succ']
    simp
  rw [h2]
  have h3 : ∑ i ∈ Finset.range (K + 1), half_ceil (F n t i) = ∑ i ∈ Finset.range K, half_ceil (F n t i) + half_ceil (F n t K) := by
    exact Finset.sum_range_succ (fun i => half_ceil (F n t i)) K
  rw [h3]
  have h4 : half_ceil (F n t K) = 0 := by
    have hz : F n t K = 0 := hk K (by omega)
    rw [hz]
    rfl
  rw [h4, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  dsimp [half_ceil, half_floor]
  omega

lemma F_sum (n t : ℕ) : ∑ i ∈ Finset.range (n + t), F n t i = n := by
  induction t with
  | zero =>
    dsimp [F]
    have h_eq : ∑ i ∈ Finset.range (n + 0), (if i = 0 then n else 0) = n := by
      rcases n with _ | n'
      · simp
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro b hb1 hb2
          rw [if_neg hb2]
        · intro h
          simp at h
    exact h_eq
  | succ t ih =>
    have hk : ∀ i ≥ n + t, F n t i = 0 := by
      intro i hi
      have h_le : n ≤ i := by omega
      exact F_zero_of_ge n t i h_le
    have h_step := F_sum_step n t (n + t) hk
    have h_eq : n + (t + 1) = n + t + 1 := by omega
    rw [h_eq]
    rw [h_step]
    exact ih

lemma F_n_minus_1_zero (n t : ℕ) (hn : 1 ≤ n) (ht : t < a n) : F n t (n - 1) = 0 := by
  by_contra h_pos
  have h_gt : F n t (n - 1) ≥ 1 := by omega
  have h_no_zero : ∀ i < n, F n t i ≥ 1 := by
    intro i hi
    by_contra h_zero
    have h_z : F n t i = 0 := by omega
    have h_next : ∀ j, i ≤ j → j ≤ n - 1 → F n t j = 0 := by
      intro j hj1 hj2
      induction j, hj1 using Nat.le_induction with
      | base => exact h_z
      | succ k hk1 ih =>
        have h_k_le : k ≤ n - 1 := by omega
        have h_zero_k := ih h_k_le
        exact F_no_internal_zeros n t k h_zero_k
    have h_end : F n t (n - 1) = 0 := h_next (n - 1) (by omega) (by omega)
    omega
  have h_sum_ge_1 : ∑ i ∈ Finset.range n, F n t i ≥ ∑ i ∈ Finset.range n, 1 := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact h_no_zero i hi
  have h_sum_ge : ∑ i ∈ Finset.range n, F n t i ≥ n := by
    have h_eq : ∑ i ∈ Finset.range n, 1 = n := by simp
    omega
  have h_sum_eq : ∑ i ∈ Finset.range (n + t), F n t i = n := F_sum n t
  have h_split : ∑ i ∈ Finset.range (n + t), F n t i = ∑ i ∈ Finset.range n, F n t i + ∑ i ∈ Finset.Ico n (n + t), F n t i := by
    exact (Finset.sum_range_add_sum_Ico (fun i => F n t i) (by omega)).symm
  have h_zero_tail : ∑ i ∈ Finset.Ico n (n + t), F n t i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact F_zero_of_ge n t i hi.1
  rw [h_split, h_zero_tail, add_zero] at h_sum_eq
  have h_eq_1 : ∀ i < n, F n t i = 1 := by
    intro i hi
    have h1 := h_no_zero i hi
    by_contra h_neq
    have h2 : F n t i ≥ 2 := by omega
    have h_sum_gt_1 : ∑ j ∈ Finset.range n, F n t j > ∑ j ∈ Finset.range n, 1 := by
      apply Finset.sum_lt_sum
      · intro j hj
        rw [Finset.mem_range] at hj
        exact h_no_zero j hj
      · use i
        constructor
        · rw [Finset.mem_range]; exact hi
        · omega
    have h_sum_gt : ∑ j ∈ Finset.range n, F n t j > n := by
      have h_eq : ∑ j ∈ Finset.range n, 1 = n := by simp
      omega
    omega
  have h_target : F n t = TargetF n := by
    funext i
    dsimp [TargetF]
    by_cases h : i < n
    · rw [if_pos h]
      exact h_eq_1 i h
    · rw [if_neg h]
      exact F_zero_of_ge n t i (by omega)
  have h_le := a_min n hn t h_target
  omega

lemma P_le_n_minus_1 (n t : ℕ) (hn : 1 ≤ n) (ht : t ≤ a n) : P n t ≤ n - 1 := by
  induction t with
  | zero =>
    dsimp [P]
    omega
  | succ t ih =>
    dsimp [P]
    have h_le : t < a n := by omega
    have h_P : P n t ≤ n - 1 := ih (by omega)
    by_cases h_eq : P n t = n - 1
    · have h_zero : F n t (n - 1) = 0 := F_n_minus_1_zero n t hn h_le
      rw [h_eq, h_zero]
      omega
    · have h_lt : P n t < n - 1 := by omega
      have h_mod : F n t (P n t) % 2 ≤ 1 := by omega
      omega

lemma P_lt_n (n : ℕ) (hn : 1 ≤ n) : P n (a n) < n := by
  have h := P_le_n_minus_1 n (a n) hn (by omega)
  omega

lemma F_eq_one_of_ge_one (n t : ℕ) (h_ge : ∀ i < n, F n t i ≥ 1) : ∀ i < n, F n t i = 1 := by
  intro i hi
  by_contra h_gt
  have h_ge_i : F n t i ≥ 1 := h_ge i hi
  have h_gt2 : F n t i ≥ 2 := by omega
  have h_sum1 : ∑ j ∈ Finset.range n, 1 < ∑ j ∈ Finset.range n, F n t j := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact h_ge j (Finset.mem_range.mp hj)
    · use i
      constructor
      · exact Finset.mem_range.mpr hi
      · omega
  have h_sum_tot : ∑ j ∈ Finset.range (n + t), F n t j = n := F_sum n t
  have h_sum_split : ∑ j ∈ Finset.range (n + t), F n t j = ∑ j ∈ Finset.range n, F n t j + ∑ j ∈ Finset.Ico n (n + t), F n t j := by
    exact (Finset.sum_range_add_sum_Ico (fun j => F n t j) (by omega)).symm
  have h_tail_z : ∑ j ∈ Finset.Ico n (n + t), F n t j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact F_zero_of_ge n t j (Finset.mem_Ico.mp hj).1
  rw [h_tail_z, add_zero] at h_sum_split
  have h_sum2 : ∑ j ∈ Finset.range n, 1 = n := by simp
  omega

lemma F_a_minus_1_val_dummy (n : ℕ) : n = n := rfl

lemma F_a_minus_1_n_minus_2_val (n : ℕ) (hn : 2 ≤ n) : F n (a n - 1) (n - 2) = 2 ∨ F n (a n - 1) (n - 2) = 3 := by
  have h_a_pos : a n > 0 := by
    by_contra h_z
    have h_a_z : a n = 0 := by omega
    have h_stable := a_is_stable n (by omega)
    rw [h_a_z] at h_stable
    have h_0 : F n 0 0 = TargetF n 0 := congrFun h_stable 0
    dsimp [F, TargetF] at h_0
    have h_pos : 0 < n := by omega
    rw [if_pos h_pos] at h_0
    omega
  have h_step : ca_step_fun (F n (a n - 1)) = TargetF n := by
    have h_a := a_is_stable n (by omega)
    have h_eq : a n - 1 + 1 = a n := by omega
    have h_F_step : F n (a n) = ca_step_fun (F n (a n - 1)) := by
      have h1 : F n (a n - 1 + 1) = ca_step_fun (F n (a n - 1)) := rfl
      rw [h_eq] at h1
      exact h1
    rw [← h_F_step]
    exact h_a
  have h_eval := congrFun h_step (n - 1)
  dsimp [TargetF] at h_eval
  rw [if_pos (by omega)] at h_eval
  dsimp [ca_step_fun] at h_eval
  have h_lt : a n - 1 < a n := by omega
  have h_n1_z : F n (a n - 1) (n - 1) = 0 := F_n_minus_1_zero n (a n - 1) (by omega) h_lt
  rw [h_n1_z] at h_eval
  have h_hc : half_ceil 0 = 0 := rfl
  rw [h_hc, zero_add] at h_eval
  have h_if : (if n - 1 = 0 then 0 else half_floor (F n (a n - 1) (n - 1 - 1))) = half_floor (F n (a n - 1) (n - 2)) := by
    have h_neq : n - 1 ≠ 0 := by omega
    rw [if_neg h_neq]
    have h_sub : n - 1 - 1 = n - 2 := by omega
    rw [h_sub]
  rw [h_if] at h_eval
  dsimp [half_floor] at h_eval
  omega

lemma F_a_minus_1_n_minus_2 (n : ℕ) (hn : 2 ≤ n) : F n (a n - 1) (n - 2) = 2 := by
  have h_a_pos : a n > 0 := by
    by_contra h_z
    have h_a_z : a n = 0 := by omega
    have h_stable := a_is_stable n (by omega)
    rw [h_a_z] at h_stable
    have h_0 : F n 0 0 = TargetF n 0 := congrFun h_stable 0
    dsimp [F, TargetF] at h_0
    have h_pos : 0 < n := by omega
    rw [if_pos h_pos] at h_0
    omega
  have h_or := F_a_minus_1_n_minus_2_val n hn
  rcases h_or with h2 | h3
  · exact h2
  · by_contra _
    have h_ge : ∀ j < n - 2, F n (a n - 1) j ≥ 1 := by
      intro j hj
      by_contra h_z
      have h_z2 : F n (a n - 1) j = 0 := by omega
      have h_next : ∀ k, j ≤ k → k ≤ n - 2 → F n (a n - 1) k = 0 := by
        intro k hk1 hk2
        induction k, hk1 using Nat.le_induction with
        | base => exact h_z2
        | succ m hm1 ih =>
          have h_m_le : m ≤ n - 2 := by omega
          exact F_no_internal_zeros n (a n - 1) m (ih h_m_le)
      have h_n2_z : F n (a n - 1) (n - 2) = 0 := h_next (n - 2) (by omega) (by omega)
      omega
    have h_sum_n : ∑ j ∈ Finset.range n, F n (a n - 1) j = (∑ j ∈ Finset.range (n - 2), F n (a n - 1) j) + F n (a n - 1) (n - 2) + F n (a n - 1) (n - 1) := by
      have e1 : Finset.range n = Finset.range (n - 1 + 1) := by congr 1; omega
      rw [e1, Finset.sum_range_succ]
      have e2 : Finset.range (n - 1) = Finset.range (n - 2 + 1) := by congr 1; omega
      rw [e2, Finset.sum_range_succ]
    have h_lt : a n - 1 < a n := by omega
    have h_n1_z : F n (a n - 1) (n - 1) = 0 := F_n_minus_1_zero n (a n - 1) (by omega) h_lt
    rw [h_n1_z, h3, add_zero] at h_sum_n
    have h_sum_n2 : ∑ j ∈ Finset.range (n - 2), F n (a n - 1) j ≥ ∑ j ∈ Finset.range (n - 2), 1 := by
      apply Finset.sum_le_sum
      intro j hj
      exact h_ge j (Finset.mem_range.mp hj)
    have h_sum_n2_eq : ∑ j ∈ Finset.range (n - 2), 1 = n - 2 := by simp
    rw [h_sum_n2_eq] at h_sum_n2
    have h_sum_n_gt : ∑ j ∈ Finset.range n, F n (a n - 1) j ≥ n + 1 := by omega
    have h_sum_tot : ∑ j ∈ Finset.range (n + (a n - 1)), F n (a n - 1) j = n := F_sum n (a n - 1)
    have h_split2 : ∑ j ∈ Finset.range (n + (a n - 1)), F n (a n - 1) j = ∑ j ∈ Finset.range n, F n (a n - 1) j + ∑ j ∈ Finset.Ico n (n + (a n - 1)), F n (a n - 1) j := by
      exact (Finset.sum_range_add_sum_Ico (fun j => F n (a n - 1) j) (by omega)).symm
    have h_tail_z : ∑ j ∈ Finset.Ico n (n + (a n - 1)), F n (a n - 1) j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact F_zero_of_ge n (a n - 1) j (Finset.mem_Ico.mp hj).1
    rw [h_tail_z, add_zero] at h_split2
    rw [← h_split2] at h_sum_n_gt
    rw [h_sum_tot] at h_sum_n_gt
    omega

lemma F_a_minus_1_ge_one (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : j < n - 2) : F n (a n - 1) j ≥ 1 := by
  by_contra h_z
  have h_z2 : F n (a n - 1) j = 0 := by omega
  have h_next : ∀ k, j ≤ k → k ≤ n - 2 → F n (a n - 1) k = 0 := by
    intro k hk1 hk2
    induction k, hk1 using Nat.le_induction with
    | base => exact h_z2
    | succ m hm1 ih =>
      have h_m_le : m ≤ n - 2 := by omega
      exact F_no_internal_zeros n (a n - 1) m (ih h_m_le)
  have h_n2_z : F n (a n - 1) (n - 2) = 0 := h_next (n - 2) (by omega) (by omega)
  have h_val := F_a_minus_1_n_minus_2 n hn
  omega

lemma F_a_minus_1_val (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : i < n - 2) : F n (a n - 1) i = 1 := by
  by_contra h_neq
  have h_ge : ∀ j < n - 2, F n (a n - 1) j ≥ 1 := F_a_minus_1_ge_one n hn
  have h_gt : F n (a n - 1) i ≥ 2 := by
    have h1 := h_ge i hi
    omega
  have h_sum_n2 : ∑ j ∈ Finset.range (n - 2), 1 < ∑ j ∈ Finset.range (n - 2), F n (a n - 1) j := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact h_ge j (Finset.mem_range.mp hj)
    · use i
      constructor
      · exact Finset.mem_range.mpr hi
      · omega
  have h_sum_n2_eq : ∑ j ∈ Finset.range (n - 2), 1 = n - 2 := by simp
  rw [h_sum_n2_eq] at h_sum_n2
  have h_sum_n : ∑ j ∈ Finset.range n, F n (a n - 1) j = (∑ j ∈ Finset.range (n - 2), F n (a n - 1) j) + F n (a n - 1) (n - 2) + F n (a n - 1) (n - 1) := by
    have e1 : Finset.range n = Finset.range (n - 1 + 1) := by congr 1; omega
    rw [e1, Finset.sum_range_succ]
    have e2 : Finset.range (n - 1) = Finset.range (n - 2 + 1) := by congr 1; omega
    rw [e2, Finset.sum_range_succ]
  have h_val_n2 := F_a_minus_1_n_minus_2 n hn
  have h_a_pos : a n > 0 := by
    by_contra h_z
    have h_a_z : a n = 0 := by omega
    have h_stable := a_is_stable n (by omega)
    rw [h_a_z] at h_stable
    have h_0 : F n 0 0 = TargetF n 0 := congrFun h_stable 0
    dsimp [F, TargetF] at h_0
    have h_pos : 0 < n := by omega
    rw [if_pos h_pos] at h_0
    omega
  have h_lt : a n - 1 < a n := by omega
  have h_n1_z : F n (a n - 1) (n - 1) = 0 := F_n_minus_1_zero n (a n - 1) (by omega) h_lt
  rw [h_n1_z, add_zero] at h_sum_n
  have h_sum_n_gt : ∑ j ∈ Finset.range n, F n (a n - 1) j > n := by omega
  have h_sum_tot : ∑ j ∈ Finset.range (n + (a n - 1)), F n (a n - 1) j = n := F_sum n (a n - 1)
  have h_split2 : ∑ j ∈ Finset.range (n + (a n - 1)), F n (a n - 1) j = ∑ j ∈ Finset.range n, F n (a n - 1) j + ∑ j ∈ Finset.Ico n (n + (a n - 1)), F n (a n - 1) j := by
    exact (Finset.sum_range_add_sum_Ico (fun j => F n (a n - 1) j) (by omega)).symm
  have h_tail_z : ∑ j ∈ Finset.Ico n (n + (a n - 1)), F n (a n - 1) j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact F_zero_of_ge n (a n - 1) j (Finset.mem_Ico.mp hj).1
  rw [h_tail_z, add_zero] at h_split2
  rw [← h_split2] at h_sum_n_gt
  rw [h_sum_tot] at h_sum_n_gt
  omega



def ContiguousGT1 (f : ℕ → ℕ) : Prop :=
  ∀ i j k, i < j → j < k → f i ≥ 2 → f k ≥ 2 → f j ≥ 2

lemma step_ge_2_implies (f : ℕ → ℕ) (i : ℕ) (h : ca_step_fun f i ≥ 2) :
    f i ≥ 2 ∨ (i > 0 ∧ f (i - 1) ≥ 2) := by
  dsimp [ca_step_fun, half_ceil, half_floor] at h
  split_ifs at h with h_eq
  · omega
  · omega

lemma ge_2_of_step (f : ℕ → ℕ) (j : ℕ) (hj : j > 0) (h1 : f j ≥ 2) (h2 : f (j - 1) ≥ 2) :
    ca_step_fun f j ≥ 2 := by
  dsimp [ca_step_fun, half_ceil, half_floor]
  split_ifs with h_eq
  · omega
  · omega

lemma ContiguousGT1_le (f : ℕ → ℕ) (h : ContiguousGT1 f) {i j k : ℕ} (hi : i ≤ j) (hj : j ≤ k) (h_i : f i ≥ 2) (h_k : f k ≥ 2) : f j ≥ 2 := by
  rcases eq_or_lt_of_le hi with rfl | hi2
  · exact h_i
  · rcases eq_or_lt_of_le hj with rfl | hj2
    · exact h_k
    · exact h i j k hi2 hj2 h_i h_k

lemma ContiguousGT1_step (f : ℕ → ℕ) (h : ContiguousGT1 f) :
    ContiguousGT1 (ca_step_fun f) := by
  intro i j k hi hj hi2 hk2
  have h_fi := step_ge_2_implies f i hi2
  have h_fk := step_ge_2_implies f k hk2
  have h_j_pos : j > 0 := by omega
  have h_fj : f j ≥ 2 := by
    rcases h_fi with h_i | h_i
    · rcases h_fk with h_k | h_k
      · exact ContiguousGT1_le f h (by omega) (by omega) h_i h_k
      · exact ContiguousGT1_le f h (by omega) (by omega) h_i h_k.2
    · rcases h_fk with h_k | h_k
      · exact ContiguousGT1_le f h (by omega) (by omega) h_i.2 h_k
      · exact ContiguousGT1_le f h (by omega) (by omega) h_i.2 h_k.2
  have h_fj1 : f (j - 1) ≥ 2 := by
    rcases h_fi with h_i | h_i
    · rcases h_fk with h_k | h_k
      · exact ContiguousGT1_le f h (by omega) (by omega) h_i h_k
      · exact ContiguousGT1_le f h (by omega) (by omega) h_i h_k.2
    · rcases h_fk with h_k | h_k
      · exact ContiguousGT1_le f h (by omega) (by omega) h_i.2 h_k
      · exact ContiguousGT1_le f h (by omega) (by omega) h_i.2 h_k.2
  exact ge_2_of_step f j h_j_pos h_fj h_fj1

lemma ContiguousGT1_F_zero (n : ℕ) : ContiguousGT1 (F n 0) := by
  intro i j k hi hj hi2 hk2
  dsimp [F] at hi2 hk2 ⊢
  split_ifs at hi2 hk2 with h1 h2
  · omega
  · omega
  · omega
  · omega

lemma ContiguousGT1_F (n t : ℕ) : ContiguousGT1 (F n t) := by
  induction t with
  | zero => exact ContiguousGT1_F_zero n
  | succ t ih =>
    have h_step : F n (t + 1) = ca_step_fun (F n t) := rfl
    rw [h_step]
    exact ContiguousGT1_step (F n t) ih

lemma P_a_minus_1_ge (n : ℕ) (hn : 4 ≤ n) : P n (a n - 1) ≥ n - 3 := by
  by_contra h_lt
  have h_P_le : P n (a n - 1) ≤ n - 4 := by omega
  have h_contig := ContiguousGT1_F (n + 1) (a n - 1)
  have h_F_np1 : F (n + 1) (a n - 1) = fun x => F n (a n - 1) x + if x = P n (a n - 1) then 1 else 0 := F_n_plus_1_eq n (a n - 1)
  have h_val_n2 := F_a_minus_1_n_minus_2 n (by omega)
  have h_val_P := F_a_minus_1_val n (by omega) (P n (a n - 1)) (by omega)
  have h_val_n3 := F_a_minus_1_val n (by omega) (n - 3) (by omega)
  have h_np1_P : F (n + 1) (a n - 1) (P n (a n - 1)) ≥ 2 := by
    have h_eq : F (n + 1) (a n - 1) (P n (a n - 1)) = F n (a n - 1) (P n (a n - 1)) + 1 := by
      have h1 := congrFun h_F_np1 (P n (a n - 1))
      rw [if_pos rfl] at h1
      exact h1
    omega
  have h_np1_n2 : F (n + 1) (a n - 1) (n - 2) ≥ 2 := by
    have h_eq : F (n + 1) (a n - 1) (n - 2) = F n (a n - 1) (n - 2) + if n - 2 = P n (a n - 1) then 1 else 0 := congrFun h_F_np1 (n - 2)
    omega
  have h_np1_n3 : F (n + 1) (a n - 1) (n - 3) = 1 := by
    have h_eq : F (n + 1) (a n - 1) (n - 3) = F n (a n - 1) (n - 3) + if n - 3 = P n (a n - 1) then 1 else 0 := congrFun h_F_np1 (n - 3)
    have h_neq : n - 3 ≠ P n (a n - 1) := by omega
    rw [if_neg h_neq] at h_eq
    omega
  have h_ge2 := h_contig (P n (a n - 1)) (n - 3) (n - 2) (by omega) (by omega) h_np1_P h_np1_n2
  omega

lemma P_a_eq (n : ℕ) (hn : 4 ≤ n) : P n (a n) = P n (a n - 1) + F n (a n - 1) (P n (a n - 1)) % 2 := by
  have h_step : P n (a n - 1 + 1) = P n (a n - 1) + F n (a n - 1) (P n (a n - 1)) % 2 := P_succ n (a n - 1)
  have h_eq : a n - 1 + 1 = a n := by
    have h_a_pos : a n > 0 := by
      by_contra h_z
      have h_a_z : a n = 0 := by omega
      have h_stable := a_is_stable n (by omega)
      rw [h_a_z] at h_stable
      have h_0 : F n 0 0 = TargetF n 0 := congrFun h_stable 0
      dsimp [F, TargetF] at h_0
      have h_pos : 0 < n := by omega
      rw [if_pos h_pos] at h_0
      omega
    omega
  rw [← h_eq]
  exact h_step

lemma chip_pos_ge_4 (n : ℕ) (hn : 4 ≤ n) : n - P n (a n) = 1 ∨ n - P n (a n) = 2 := by
  have hP_ge := P_a_minus_1_ge n hn
  have hP_lt := P_lt_n n (by omega)
  have hP_step := P_a_eq n hn
  have h_val_n2 := F_a_minus_1_n_minus_2 n (by omega)
  have h_val_n3 := F_a_minus_1_val n (by omega) (n - 3) (by omega)
  have h_val_n1 : F n (a n - 1) (n - 1) = 0 := by
    have h_a_pos : a n > 0 := by
      by_contra h_z
      have h_a_z : a n = 0 := by omega
      have h_stable := a_is_stable n (by omega)
      rw [h_a_z] at h_stable
      have h_0 : F n 0 0 = TargetF n 0 := congrFun h_stable 0
      dsimp [F, TargetF] at h_0
      have h_pos : 0 < n := by omega
      rw [if_pos h_pos] at h_0
      omega
    have h_lt : a n - 1 < a n := by omega
    exact F_n_minus_1_zero n (a n - 1) (by omega) h_lt
  rcases eq_or_lt_of_le hP_ge with h_eq3 | h_lt3
  · have h_eq_3 : P n (a n - 1) = n - 3 := h_eq3.symm
    have h_mod : F n (a n - 1) (P n (a n - 1)) % 2 = 1 := by
      rw [h_eq_3, h_val_n3]
    rw [h_mod] at hP_step
    omega
  · have h_ge2 : P n (a n - 1) ≥ n - 2 := by omega
    rcases eq_or_lt_of_le h_ge2 with h_eq2 | h_lt2
    · have h_eq_2 : P n (a n - 1) = n - 2 := h_eq2.symm
      have h_mod : F n (a n - 1) (P n (a n - 1)) % 2 = 0 := by
        rw [h_eq_2, h_val_n2]
      rw [h_mod] at hP_step
      omega
    · have h_eq_1 : P n (a n - 1) = n - 1 := by omega
      have h_mod : F n (a n - 1) (P n (a n - 1)) % 2 = 0 := by
        rw [h_eq_1, h_val_n1]
      rw [h_mod] at hP_step
      omega

lemma chip_pos_1 : 1 - P 1 (a 1) = 1 ∨ 1 - P 1 (a 1) = 2 := by
  have h_a1 : a 1 = 0 := by
    have h1 : F 1 0 = TargetF 1 := by
      funext i
      dsimp [F, TargetF]
      split_ifs <;> omega
    have h_le := a_min 1 (by omega) 0 h1
    omega
  rw [h_a1]
  dsimp [P]
  omega

lemma chip_pos_2 : 2 - P 2 (a 2) = 1 ∨ 2 - P 2 (a 2) = 2 := by
  have h_a2 : a 2 = 1 := by
    have h1 : F 2 1 = TargetF 2 := by
      funext i
      have h_cases : i = 0 ∨ i = 1 ∨ i ≥ 2 := by omega
      rcases h_cases with rfl | rfl | hi
      · rfl
      · rfl
      · have hf : F 2 1 i = 0 := F_zero_of_ge 2 1 i hi
        have ht : TargetF 2 i = 0 := by
          dsimp [TargetF]
          rw [if_neg (by omega)]
        rw [hf, ht]
    have h2 : F 2 0 ≠ TargetF 2 := by
      intro h
      have h0 := congrFun h 0
      dsimp [F, TargetF] at h0
      omega
    have h_le := a_min 2 (by omega) 1 h1
    have h_not_0 : a 2 ≠ 0 := by
      intro h
      have h_stable := a_is_stable 2 (by omega)
      rw [h] at h_stable
      exact h2 h_stable
    omega
  rw [h_a2]
  dsimp [P, F]
  omega

lemma chip_pos_3 : 3 - P 3 (a 3) = 1 ∨ 3 - P 3 (a 3) = 2 := by
  have h_a3 : a 3 = 3 := by
    have h1 : F 3 3 = TargetF 3 := by
      funext i
      have h_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i ≥ 3 := by omega
      rcases h_cases with rfl | rfl | rfl | hi
      · rfl
      · rfl
      · rfl
      · have hf : F 3 3 i = 0 := F_zero_of_ge 3 3 i hi
        have ht : TargetF 3 i = 0 := by
          dsimp [TargetF]
          rw [if_neg (by omega)]
        rw [hf, ht]
    have h0 : F 3 0 ≠ TargetF 3 := by
      intro h
      have h0 := congrFun h 0
      dsimp [F, TargetF] at h0
      omega
    have h1_not : F 3 1 ≠ TargetF 3 := by
      intro h
      have h0 := congrFun h 0
      dsimp [F, ca_step_fun, half_ceil, half_floor, TargetF] at h0
      omega
    have h2_not : F 3 2 ≠ TargetF 3 := by
      intro h
      have h1_val := congrFun h 1
      dsimp [F, ca_step_fun, half_ceil, half_floor, TargetF] at h1_val
      omega
    have h_le := a_min 3 (by omega) 3 h1
    have h_not_0 : a 3 ≠ 0 := by intro h; have h_s := a_is_stable 3 (by omega); rw [h] at h_s; exact h0 h_s
    have h_not_1 : a 3 ≠ 1 := by intro h; have h_s := a_is_stable 3 (by omega); rw [h] at h_s; exact h1_not h_s
    have h_not_2 : a 3 ≠ 2 := by intro h; have h_s := a_is_stable 3 (by omega); rw [h] at h_s; exact h2_not h_s
    omega
  rw [h_a3]
  dsimp [P, F, ca_step_fun, half_ceil, half_floor]
  omega

lemma chip_pos (n : ℕ) (hn : 1 ≤ n) : n - P n (a n) = 1 ∨ n - P n (a n) = 2 := by
  rcases lt_trichotomy n 2 with h1 | h2 | h3
  · have : n = 1 := by omega
    subst this
    exact chip_pos_1
  · subst h2
    exact chip_pos_2
  · rcases eq_or_lt_of_le (show 3 ≤ n by omega) with h3_eq | h3_lt
    · subst h3_eq
      exact chip_pos_3
    · exact chip_pos_ge_4 n (by omega)

-- EVOLVE-BLOCK-END


theorem target_theorem_0
  : ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  -- EVOLVE-BLOCK-START
  intro n hn
  have hc : n - P n (a n) = 1 ∨ n - P n (a n) = 2 := chip_pos n hn
  have hd : a (n + 1) = a n + (n - P n (a n)) := coupling_diff n hn (by omega)
  omega
  -- EVOLVE-BLOCK-END
