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

import Mathlib.Computability.TuringMachine
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.PartENat


/-! # Turing Machines, Busy Beaver version.
A variant on the definition of the TM0 model in Mathlib: while the statements the
`TM` can make in the usual `TM0` are split into two categories (either write at the
current position or move left/right), we want to combine the two to stick to the
`BB` convention: first write at the current position and then move left/right.

Note that this Turing Machine model also works with states of type `Option Γ`. This
is because in the busy beaver context, the turing machines also have an addition
"halting" state

See also https://git.sr.ht/~vigoux/busybeaver for a different approach to formalising
these objects.
-/

namespace Turing

open Mathlib
open Relation

open Nat

namespace BusyBeaver

section

-- type of tape symbols
variable (Γ : Type*)

-- type of "labels" or TM states
variable (Λ : Type*)

/-- A Turing machine "statement" is just a command to write a symbol on the tape
(at the current position) and then move left or right-/
structure Stmt where write ::
  symbol : Γ
  dir : Dir
deriving Inhabited

/-- A Post-Turing machine with symbol type `Γ` and label type `Λ`
  is a function which, given the current state `q : Λ` and
  the tape head `a : Γ`, either halts (returns `none`) or returns
  a new state `q' : Option Λ` and a `Stmt` describing what to do: a
  command to write a symbol and move left or right. Notice that there
  are two ways of halting at a given `(state, head)` pair: either
  the machine halts immediatly (i.e. the function returns `none`),
  or the machine moves to the "halting state", i.e. `none : Option Λ`
  and performs one last action.

  Typically, both `Λ` and `Γ` are required to be inhabited; the default value
  for `Γ` is the "blank" tape value, and the default value of `Λ` is
  the initial state. -/
@[nolint unusedArguments]
def Machine [Inhabited Λ] :=
  Λ → Γ → Option (Option Λ × (Stmt Γ))

instance Machine.inhabited [Inhabited Λ] : Inhabited (Machine Γ Λ) := by
  unfold Machine; infer_instance

/-- The configuration state of a Turing machine during operation
  consists of a label (machine state), and a tape.
  The tape is represented in the form `(a, L, R)`, meaning the tape
  looks like `L.rev ++ [a] ++ R` with the machine currently reading
  the `a`. The lists are automatically extended with blanks as the
  machine moves around. -/
structure Cfg [Inhabited Γ] where
  /-- The current machine state. -/
  q : Option Λ
  /-- The current state of the tape: current symbol, left and right parts. -/
  tape : Tape Γ

variable {Γ Λ}
variable [Inhabited Λ]

variable [Inhabited Γ]

instance Cfg.inhabited : Inhabited (Cfg Γ Λ) := ⟨⟨default, default⟩⟩

namespace Machine

/-- Execution semantics of the Turing machine. -/
def step (M : Machine Γ Λ) : Cfg Γ Λ → Option (Cfg Γ Λ)
| ⟨none, _⟩ => none
| ⟨some q, T⟩ => (M q T.1).map
    fun ⟨q', a⟩ ↦ ⟨q', match a with
    | Stmt.write a d => (T.write a).move d⟩


/-- The statement `Reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def Reaches (M : Machine Γ Λ) : Cfg Γ Λ → Cfg Γ Λ → Prop := ReflTransGen fun a b ↦ b ∈ step M a

/-- The initial configuration. -/
def init (l : List Γ) : Cfg Γ Λ := ⟨default, Tape.mk₁ l⟩

def eval₀ (M : Machine Γ Λ) (s : Cfg Γ Λ) : Part (Cfg Γ Λ) :=
  (Turing.eval (step M) s)

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : Machine Γ Λ) (l : List Γ) : Part (ListBlank Γ) :=
  (Turing.eval (step M) (init l)).map fun c ↦ c.tape.right₀

def multiStep (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) : Option (Cfg Γ Λ) :=
    (Option.bind · (step M))^[n] config

@[simp]
lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : M.multiStep config 0 = some config :=
  rfl

@[simp]
lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : M.multiStep config 1 = M.step config :=
  rfl

lemma Option.bind_iterate {α} (f : α → Option α) (a : Option α) (n : ℕ)  :
    (Option.bind · f)^[n+1] a = Option.bind ((Option.bind · f)^[n] a) f := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ', Function.comp_apply, ih]

lemma Option.bind_iterate' {α} (f : α → Option α) (a : Option α) (n : ℕ)  :
    (Option.bind · f)^[n+1] a = (Option.bind · f)^[n] (a.bind f) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ, Function.comp_apply, ih]

@[simp]
lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    M.multiStep config (n + 1) = Option.bind (M.multiStep config n) M.step := by
  rw [multiStep, Option.bind_iterate, multiStep]

lemma dom_of_apply_eq_none  {σ : Type*} {f : σ → Option σ} {s : σ} (hf : f s = none) :
    s ∈ Turing.eval f s := by
  apply PFun.fix_stop
  simp [hf]

theorem temp  {σ : Type*} {f : σ → Option σ} {s t : σ} (H : t ∈ Turing.eval f s) :
    Turing.Reaches f s t := by
  rw [mem_eval] at H
  exact H.left

@[simp]
theorem Turing.apply_get_eval {σ : Type*} {f : σ → Option σ} {s : σ} (H : (Turing.eval f s).Dom) :
    f ((Turing.eval f s).get H) = none := by
  have := Part.get_mem H
  rw [mem_eval] at this
  exact this.right

theorem get_eq_get {σ : Type*} (a b : Part σ) (ha : a.Dom) :
    a.get ha ∈ b → a = b := by
  intro H
  have hb : b.Dom := by
    rw [Part.dom_iff_mem]
    use a.get ha
  rw [← Part.eq_get_iff_mem hb] at H
  ext c
  rw [← Part.eq_get_iff_mem ha, ← Part.eq_get_iff_mem hb, H]

theorem dom_eval_of_dom {σ : Type*} {f : σ → Option σ} {s : σ} (H : (Turing.eval f s).Dom) :
    (Turing.eval f ((Turing.eval f s).get H)).Dom := by
  suffices Turing.eval f ((Turing.eval f s).get H) = Turing.eval f s by
    rwa [this]
  have : (Turing.eval f s).get H ∈ Turing.eval f ((Turing.eval f s).get H) := by
    apply dom_of_apply_eq_none
    simp
  symm
  apply get_eq_get _ _ H this

theorem eval_eq_eval {σ : Type*} {f : σ → Option σ} {a a' : σ} (H : f a = some a'):
    Turing.eval f a = Turing.eval f a' := by
  set C : σ → Prop := fun s ↦ f a = some s →Turing.eval f a = Turing.eval f a' with hC
  apply reaches_eval
  rw [Turing.Reaches]
  apply ReflTransGen.single
  rw [H]
  rfl
  -- apply evalInduction (C := C) (a := a') _ H

theorem eval_dom_iff₀ {σ : Type*} {f : σ → Option σ} {s : σ} (H : (Turing.eval f s).Dom):
    ∃ n, ((Option.bind · f)^[n+1] s).isNone := by
  let b := (Part.get _ H)
  set C : σ → Prop := fun s ↦ (Turing.eval f s).Dom → ∃ n, ((Option.bind · f)^[n+1] s).isNone with hC
  apply evalInduction (C := C) (a := s) (h := Part.get_mem H) _ H
  intro a ha h HH
  obtain ha | ⟨a', ha'⟩ := (f a).eq_none_or_eq_some
  · use 0
    simp [ha]
  · obtain ⟨n, hn⟩ := h a' ha' (by rwa [←eval_eq_eval ha'])
    use n+1
    simp at hn
    simp [Option.bind_iterate', Option.some_bind, ha', Option.bind_iterate', Option.some_bind, hn]

theorem eval_dom_iff₁ {σ : Type*} (f : σ → Option σ) (s : σ)
    (H : ∃ n, ((Option.bind · f)^[n+1] s) = none):
    (Turing.eval f s).Dom := by
  obtain ⟨n, hn⟩ := H
  induction n generalizing s with
  | zero =>
    simp at hn
    rw [Part.dom_iff_mem]
    exact ⟨s, dom_of_apply_eq_none hn⟩
  | succ n ih =>
    obtain ha | ⟨a', ha'⟩ := (f s).eq_none_or_eq_some
    · rw [Part.dom_iff_mem]
      exact ⟨s, dom_of_apply_eq_none ha⟩
    · simp_rw [Option.bind_iterate', Option.some_bind] at hn ih
      simp_rw [ha', Option.some_bind] at hn
      have ih := ih a' hn
      rwa [eval_eq_eval ha']

variable {Γ Λ : Type*} [Inhabited Λ] [Inhabited Γ] --[Fintype Γ] [Fintype Λ]
variable (M : Machine Γ Λ)

/--
`M.IsHaltingInput l` is the predicate that `M` is a halting configuration for `M`.
-/
def IsHaltingInput (l : List Γ) : Prop := (eval M l).Dom


-- TODO(Paul-Lez): Do we actually need this?
/--
`M.HaltsAtConfiguration s` is the predicate that `M` is a halting configuration for `M`.
-/
def IsHaltingConfiguration (s : Cfg Γ Λ) : Prop := (step M s).isNone

/--
The property that a Turing Machine `M` eventually halts when starting from an empty tape
-/
class IsHalting : Prop where
  halts : M.IsHaltingInput []

/--
The predicate that a machine starting at configuration `s` stops after at most `n` steps.
-/
def HaltsAfter (s : Cfg Γ Λ) (n : ℕ) : Prop :=
  ((Option.bind · (step M))^[n+1] s).isNone

lemma haltsAfter_zero_iff (s : Cfg Γ Λ) :
    HaltsAfter M s 0 ↔ step M s = none := by
  rw [HaltsAfter, Function.iterate_one, Option.some_bind, Option.isNone_iff_eq_none]

lemma exists_haltsAt_of_isHalting [IsHalting M] : ∃ n, M.HaltsAfter (init []) n := by
  apply eval_dom_iff₀ IsHalting.halts

noncomputable def haltingNumber
    (M : Machine Γ Λ) : PartENat :=
  --The smallest `n` such that `M` halts after `n` steps when starting from an empty tape.
  --If no such `n` exists then this is equal to `⊤`.
  sInf {(n : PartENat) |  (n : ℕ) (_ : HaltsAfter M (init []) n) }

end Machine

end BusyBeaver

end Turing
