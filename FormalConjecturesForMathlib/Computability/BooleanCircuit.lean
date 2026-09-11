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

public import FormalConjecturesForMathlib.Computability.BooleanTruthTable

/-!
# Typed De Morgan circuits

A straight-line program may read its inputs and previously computed gates, with
unrestricted reuse. References are typed: cycles and missing gates cannot occur.
The single output may also be an input. NOT gates are free; each binary AND/OR
gate costs one. There are no primitive constant gates.

This is the basis and size convention of Ilango, *SAT Reduces to the Minimum
Circuit Size Problem with a Random Oracle*, §2.2 (ordinary, oracle-free circuits):
https://eccc.weizmann.ac.il/report/2023/165/.
It also agrees with the AND/OR cost convention in Hirahara's Appendix C:
https://eccc.weizmann.ac.il/report/2022/119/.
-/

@[expose] public section

namespace BooleanCircuit

/-- Unary NOT and binary AND/OR gates. -/
inductive Gate (α : Type*)
  | not (a : α)
  | and (a b : α)
  | or (a b : α)

namespace Gate

/-- Boolean evaluation of a gate from its input values. -/
def eval {α : Type*} (v : α → Bool) : Gate α → Bool
  | not a => !(v a)
  | and a b => v a && v b
  | or a b => v a || v b

/-- Only AND and OR gates contribute to circuit size. -/
def cost {α : Type*} : Gate α → ℕ
  | not _ => 0
  | and _ _ | or _ _ => 1

end Gate

/-- A straight-line program with inputs in σ and k already available gate values.
The newest gate is at index zero. A reference may be used any number of times. -/
inductive Program (σ : Type*) : ℕ → Type _
  | output {k : ℕ} (ref : σ ⊕ Fin k) : Program σ k
  | step {k : ℕ} (gate : Gate (σ ⊕ Fin k)) (rest : Program σ (k + 1)) : Program σ k

namespace Program

/-- Evaluate every instruction, then return the specified output. -/
def eval {σ : Type*} {k : ℕ} (v : σ → Bool) (env : Fin k → Bool) :
    Program σ k → Bool
  | output ref => Sum.elim v env ref
  | step gate rest => rest.eval v (Fin.cons (gate.eval (Sum.elim v env)) env)

/-- The number of binary gates, counting a shared gate just once. -/
def size {σ : Type*} {k : ℕ} : Program σ k → ℕ
  | output _ => 0
  | step gate rest => gate.cost + rest.size

/-- The number of all instructions, including the free NOT gates. -/
def gateCount {σ : Type*} {k : ℕ} : Program σ k → ℕ
  | output _ => 0
  | step _ rest => 1 + rest.gateCount

theorem size_le_gateCount {σ : Type*} {k : ℕ} (p : Program σ k) :
    p.size ≤ p.gateCount := by
  induction p with
  | output ref => exact Nat.le_refl _
  | step gate rest ih =>
    cases gate <;> simp only [size, gateCount, Gate.cost] <;> omega

/-- Negate the output, adding only a free NOT gate. -/
def neg {σ : Type*} {k : ℕ} : Program σ k → Program σ k
  | output ref => step (.not ref) (output (.inr 0))
  | step gate rest => step gate rest.neg

@[simp]
theorem size_neg {σ : Type*} {k : ℕ} (p : Program σ k) : p.neg.size = p.size := by
  induction p with
  | output ref => rfl
  | step gate rest ih => simp [neg, size, ih]

@[simp]
theorem eval_neg {σ : Type*} {k : ℕ} (p : Program σ k) (v : σ → Bool)
    (env : Fin k → Bool) : p.neg.eval v env = !(p.eval v env) := by
  induction p with
  | output ref => rfl
  | step gate rest ih => exact ih _

/-- Append one identity AND gate, increasing size by exactly one. -/
def pad {σ : Type*} {k : ℕ} : Program σ k → Program σ k
  | output ref => step (.and ref ref) (output (.inr 0))
  | step gate rest => step gate rest.pad

@[simp]
theorem size_pad {σ : Type*} {k : ℕ} (p : Program σ k) :
    p.pad.size = p.size + 1 := by
  induction p with
  | output ref => rfl
  | step gate rest ih => simp [pad, size, ih, Nat.add_assoc]

@[simp]
theorem eval_pad {σ : Type*} {k : ℕ} (p : Program σ k) (v : σ → Bool)
    (env : Fin k → Bool) : p.pad.eval v env = p.eval v env := by
  induction p with
  | output ref => simp [pad, eval, Gate.eval]
  | step gate rest ih => exact ih _

/-- Add any prescribed number of identity AND gates. -/
def padMany {σ : Type*} {k : ℕ} (p : Program σ k) : ℕ → Program σ k
  | 0 => p
  | t + 1 => (p.padMany t).pad

@[simp]
theorem size_padMany {σ : Type*} {k : ℕ} (p : Program σ k) (t : ℕ) :
    (p.padMany t).size = p.size + t := by
  induction t with
  | zero => simp [padMany]
  | succ t ih => simp [padMany, ih, Nat.add_assoc]

@[simp]
theorem eval_padMany {σ : Type*} {k : ℕ} (p : Program σ k) (t : ℕ)
    (v : σ → Bool) (env : Fin k → Bool) :
    (p.padMany t).eval v env = p.eval v env := by
  induction t with
  | zero => rfl
  | succ t ih => simp [padMany, ih]

end Program

/-- A circuit starts with no gate values. -/
abbrev Circuit (σ : Type*) := Program σ 0

namespace Circuit

/-- The Boolean function computed by a circuit. -/
def eval {σ : Type*} (c : Circuit σ) (v : σ → Bool) : Bool :=
  Program.eval v Fin.elim0 c

/-- Without primitive constants or inputs, there is no circuit output. -/
theorem not_nonempty_zero : ¬ Nonempty (Circuit (Fin 0)) := by
  have h : ∀ r : Fin 0 ⊕ Fin 0, False := fun r => Sum.elim Fin.elim0 Fin.elim0 r
  rintro ⟨c⟩
  cases c with
  | output ref => exact h ref
  | step gate rest =>
    cases gate with
    | not ref => exact h ref
    | and ref other => exact h ref
    | or ref other => exact h ref

end Circuit

end BooleanCircuit
