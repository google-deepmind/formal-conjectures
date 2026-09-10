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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite-program randomized word RAM

Words and addresses are reduced modulo 2^w. Programs have finitely many
instructions, fixed register names and jump labels. Memory starts at zero and
changes only through store instructions. The read-only input is an explicit
bitstring with random access. A coin instruction consumes one fresh random bit.
Arithmetic, comparisons, word bit operations, loads and stores each cost one step.

Reference for the model: MIT 6.006, Spring 2020, Recitation 1, p.4:
https://ocw.mit.edu/courses/6-006-introduction-to-algorithms-spring-2020/c6d8f06c6f11e3342633dec85498f551_MIT6_006S20_r01.pdf.
Fine-grained word-size convention: Vassilevska Williams, *On some fine-grained
questions in algorithms and complexity*, §2.1:
https://people.csail.mit.edu/virgi/eccentri.pdf.

Registers store unsigned words; signed data are represented by their explicit
bitstring encoding. Division by zero returns zero; oversized shifts return zero.
Falling outside the program halts with false. Time measures executed instructions,
not the evaluation cost of this Lean interpreter.
-/

@[expose] public section

namespace WordRAM

/-- Word truncation, used for every register write and memory address. -/
def word (w x : ℕ) : ℕ := x % 2 ^ w

theorem word_lt (w x : ℕ) : word w x < 2 ^ w :=
  Nat.mod_lt _ (Nat.pow_pos (by decide))

@[simp]
theorem word_word (w x : ℕ) : word w (word w x) = word w x := by
  simp [word]

/-- Arithmetic and Boolean operations on two machine words. -/
inductive BinaryOp
  | add | sub | mul | div | mod | bitAnd | bitOr | bitXor | shiftLeft | shiftRight
  deriving DecidableEq

/-- Evaluate a word operation, including modular subtraction. -/
def BinaryOp.eval (op : BinaryOp) (w a b : ℕ) : ℕ :=
  let a := word w a
  let b := word w b
  word w <| match op with
    | .add => a + b
    | .sub => a + 2 ^ w - b
    | .mul => a * b
    | .div => a / b
    | .mod => a % b
    | .bitAnd => Nat.land a b
    | .bitOr => Nat.lor a b
    | .bitXor => Nat.xor a b
    | .shiftLeft => if b < w then Nat.shiftLeft a b else 0
    | .shiftRight => if b < w then Nat.shiftRight a b else 0

theorem BinaryOp.eval_lt (op : BinaryOp) (w a b : ℕ) : op.eval w a b < 2 ^ w :=
  word_lt _ _

/-- Comparison conditions on unsigned words. -/
inductive Comparison
  | equal | less
  deriving DecidableEq

def Comparison.eval (op : Comparison) (a b : ℕ) : Bool :=
  match op with
  | .equal => a == b
  | .less => a < b

/-- Registers are fixed program identifiers; memory addresses are register values. -/
inductive Instruction
  | literal (dst value : ℕ)
  | copy (dst src : ℕ)
  | binary (dst : ℕ) (op : BinaryOp) (left right : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | readInput (dst address : ℕ)
  | inputLength (dst : ℕ)
  | wordWidth (dst : ℕ)
  | branch (op : Comparison) (left right yes no : ℕ)
  | jump (label : ℕ)
  | coin (dst : ℕ)
  | halt (src : ℕ)
  deriving DecidableEq

/-- A single fixed finite instruction list. -/
abbrev Program := List Instruction

/-- A configuration; input and random bits are supplied separately. -/
structure State where
  pc : ℕ := 0
  registers : ℕ → ℕ := fun _ => 0
  memory : ℕ → ℕ := fun _ => 0
  nextCoin : ℕ := 0

/-- Update one register, truncating its value and advancing the program counter. -/
def State.write (s : State) (w dst value : ℕ) : State :=
  {s with pc := s.pc + 1, registers := Function.update s.registers dst (word w value)}

@[simp]
theorem State.write_read (s : State) (w dst value : ℕ) :
    (s.write w dst value).registers dst = word w value := by
  simp [State.write]

theorem State.write_other (s : State) (w dst value i : ℕ) (h : i ≠ dst) :
    (s.write w dst value).registers i = s.registers i := by
  simp [State.write, h]

/-- One instruction returns either a Boolean answer or the next configuration. -/
def step (p : Program) (w : ℕ) (input coins : List Bool) (s : State) : Bool ⊕ State :=
  let r := fun i => word w (s.registers i)
  match p[s.pc]? with
  | none => .inl false
  | some (.literal dst value) => .inr (s.write w dst value)
  | some (.copy dst src) => .inr (s.write w dst (r src))
  | some (.binary dst op a b) => .inr (s.write w dst (op.eval w (r a) (r b)))
  | some (.load dst a) => .inr (s.write w dst (s.memory (r a)))
  | some (.store a src) => .inr
      {s with pc := s.pc + 1, memory := Function.update s.memory (r a) (r src)}
  | some (.readInput dst a) =>
      .inr (s.write w dst (if input[r a]?.getD false then 1 else 0))
  | some (.inputLength dst) => .inr (s.write w dst input.length)
  | some (.wordWidth dst) => .inr (s.write w dst w)
  | some (.branch op a b yes no) =>
      .inr {s with pc := if op.eval (r a) (r b) then yes else no}
  | some (.jump label) => .inr {s with pc := label}
  | some (.coin dst) =>
      .inr {s.write w dst (if coins[s.nextCoin]?.getD false then 1 else 0) with
        nextCoin := s.nextCoin + 1}
  | some (.halt src) => .inl (r src != 0)

/-- Each step consumes at most one fresh random bit. -/
theorem step_coin_bound {p : Program} {w : ℕ} {input coins : List Bool} {s t : State}
    (h : step p w input coins s = .inr t) : t.nextCoin ≤ s.nextCoin + 1 := by
  unfold step at h
  split at h
  all_goals cases h <;> simp [State.write]

/-- Consumed random bits are never read again. -/
theorem step_coin_mono {p : Program} {w : ℕ} {input coins : List Bool} {s t : State}
    (h : step p w input coins s = .inr t) : s.nextCoin ≤ t.nextCoin := by
  unfold step at h
  split at h
  all_goals cases h <;> simp [State.write]

/-- A step can inspect only the next random bit, and no other part of its tape. -/
theorem step_eq_of_coin_eq (p : Program) (w : ℕ) (input coins coins' : List Bool)
    (s : State) (h : coins[s.nextCoin]?.getD false = coins'[s.nextCoin]?.getD false) :
    step p w input coins s = step p w input coins' s := by
  simp only [step, h]

/-- Execute at most t instructions; none means the time budget was exhausted. -/
def run (p : Program) (w : ℕ) (input coins : List Bool) : ℕ → State → Option Bool
  | 0, _ => none
  | t + 1, s =>
      match step p w input coins s with
      | .inl b => some b
      | .inr s' => run p w input coins t s'

/-- Run from zero registers, zero memory and the first instruction. -/
def execute (p : Program) (w : ℕ) (input coins : List Bool) (t : ℕ) : Option Bool :=
  run p w input coins t {}

/-- A t-step computation depends only on the next t random bits. -/
theorem run_eq_of_coins (p : Program) (w : ℕ) (input coins coins' : List Bool)
    (t : ℕ) (s : State)
    (h : ∀ i, s.nextCoin ≤ i → i < s.nextCoin + t →
      coins[i]?.getD false = coins'[i]?.getD false) :
    run p w input coins t s = run p w input coins' t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    simp only [run]
    rw [step_eq_of_coin_eq p w input coins coins' s (h _ (by omega) (by omega))]
    cases hs : step p w input coins' s with
    | inl b => rfl
    | inr s' =>
      apply ih
      intro i hi hj
      have hlo := step_coin_mono hs
      have hhi := step_coin_bound hs
      exact h i (by omega) (by omega)

/-- Extra random bits beyond the time budget cannot affect the result. -/
theorem execute_append_coins (p : Program) (w : ℕ) (input coins extra : List Bool)
    (t : ℕ) (ht : t ≤ coins.length) :
    execute p w input (coins ++ extra) t = execute p w input coins t := by
  apply run_eq_of_coins
  intro i _ hi
  change i < 0 + t at hi
  rw [List.getElem?_append_left (by omega)]

/-- An established output remains the same when the instruction budget increases. -/
theorem run_mono {p : Program} {w : ℕ} {input coins : List Bool} {t u : ℕ}
    {s : State} {b : Bool} (h : run p w input coins t s = some b) (htu : t ≤ u) :
    run p w input coins u s = some b := by
  induction t generalizing u s with
  | zero => simp [run] at h
  | succ t ih =>
    cases u with
    | zero => omega
    | succ u =>
      simp only [run] at h ⊢
      split at h
      · simp_all
      · exact ih h (by omega)

/-- The number of t-bit random tapes on which the machine returns the specified answer. -/
def correctCount (p : Program) (w : ℕ) (input : List Bool) (t : ℕ) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun v : Fin t → Bool =>
    execute p w input (List.ofFn v) t = some b)).card

/-- Bounded-error computation: all tapes halt within t steps and at least
two thirds of the uniformly sampled tapes return the specified answer. -/
def BoundedError (p : Program) (w : ℕ) (input : List Bool) (t : ℕ) (b : Bool) : Prop :=
  (∀ v : Fin t → Bool, (execute p w input (List.ofFn v) t).isSome = true) ∧
    2 * 2 ^ t ≤ 3 * correctCount p w input t b

instance (p : Program) (w : ℕ) (input : List Bool) (t : ℕ) (b : Bool) :
    Decidable (BoundedError p w input t b) := by
  unfold BoundedError
  infer_instance

/-- Returning the correct answer on every tape gives success probability one. -/
theorem boundedError_of_certain {p : Program} {w : ℕ} {input : List Bool} {t : ℕ}
    {b : Bool} (h : ∀ v : Fin t → Bool, execute p w input (List.ofFn v) t = some b) :
    BoundedError p w input t b := by
  constructor
  · intro v
    simp [h v]
  · have hc : correctCount p w input t b = 2 ^ t := by simp [correctCount, h]
    rw [hc]
    omega

theorem correctCount_le (p : Program) (w : ℕ) (input : List Bool) (t : ℕ) (b : Bool) :
    correctCount p w input t b ≤ 2 ^ t := by
  calc
    _ ≤ Fintype.card (Fin t → Bool) := Finset.card_le_univ _
    _ = 2 ^ t := by simp

/-- True and false outputs account for disjoint subsets of the random tapes. -/
theorem correctCount_add_le (p : Program) (w : ℕ) (input : List Bool) (t : ℕ) :
    correctCount p w input t true + correctCount p w input t false ≤ 2 ^ t := by
  let yes := Finset.univ.filter (fun v : Fin t → Bool =>
    execute p w input (List.ofFn v) t = some true)
  let no := Finset.univ.filter (fun v : Fin t → Bool =>
    execute p w input (List.ofFn v) t = some false)
  have hd : Disjoint yes no := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    simp only [yes, no, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
    rw [hv] at hw
    cases hw
  calc
    _ = (yes ∪ no).card := (Finset.card_union_of_disjoint hd).symm
    _ ≤ Fintype.card (Fin t → Bool) := Finset.card_le_univ _
    _ = 2 ^ t := by simp

/-- At the two-thirds threshold, a machine cannot decide both answers. -/
theorem boundedError_unique {p : Program} {w : ℕ} {input : List Bool} {t : ℕ}
    {a b : Bool} (ha : BoundedError p w input t a) (hb : BoundedError p w input t b) :
    a = b := by
  have hc := correctCount_add_le p w input t
  have hp : 0 < 2 ^ t := Nat.pow_pos (by decide)
  have h1 := ha.2
  have h2 := hb.2
  cases a <;> cases b <;> first | rfl | omega

/-- A program which times out on every tape is not a bounded-error decider. -/
theorem not_boundedError_zero (p : Program) (w : ℕ) (input : List Bool) (b : Bool) :
    ¬ BoundedError p w input 0 b := by
  rintro ⟨h, _⟩
  have := h Fin.elim0
  simp [execute, run] at this

/-- A logarithmic word width with one global positive coefficient. -/
def logarithmicWidth (c size : ℕ) : ℕ := c * (Nat.log2 (size + 2) + 1)

theorem input_fits (size : ℕ) :
    size < 2 ^ logarithmicWidth 1 size := by
  simpa [logarithmicWidth, Nat.log2_eq_log_two] using
    (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2))
      (Nat.lt_pow_succ_log_self (by decide) (size + 2)).le)

/-- One fixed program and word-size coefficient decide all promised encoded inputs
within a fixed constant multiple of the specified input-dependent time bound. -/
def HasFastDecider {α : Type} [BitstringEncoding α]
    (valid : α → Prop) (answer : α → Bool) (time : α → ℕ) : Prop :=
  ∃ (p : Program) (c C : ℕ), 1 ≤ c ∧ 1 ≤ C ∧ ∀ x, valid x →
    BoundedError p (logarithmicWidth c (BitstringEncoding.bitEncode x).length)
      (BitstringEncoding.bitEncode x) (C * time x) (answer x)

/-- A rational power time bound, without real rounding: t^b ≤ C (n+1)^a f(x).
The denominator must be positive. The time witness may vary with the input,
but the program, word-width coefficient and multiplicative constant are fixed. -/
def HasPowerTimeDecider {α : Type} [BitstringEncoding α]
    (valid : α → Prop) (answer : α → Bool) (size factor : α → ℕ) (a b : ℕ) : Prop :=
  0 < b ∧ ∃ (p : Program) (c C : ℕ), 1 ≤ c ∧ 1 ≤ C ∧ ∀ x, valid x →
    ∃ t : ℕ, t ^ b ≤ C * (size x + 1) ^ a * factor x ∧
      BoundedError p (logarithmicWidth c (BitstringEncoding.bitEncode x).length)
        (BitstringEncoding.bitEncode x) t (answer x)

theorem not_hasPowerTimeDecider_zero {α : Type} [BitstringEncoding α]
    (valid : α → Prop) (answer : α → Bool) (size factor : α → ℕ) (a : ℕ) :
    ¬ HasPowerTimeDecider valid answer size factor a 0 := by
  simp [HasPowerTimeDecider]

end WordRAM
