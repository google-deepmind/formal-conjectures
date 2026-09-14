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
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.Forall2

/-!
# Explicit Boolean truth tables

Rows are all assignments in lexicographic order, with the first variable most
significant. Partial tables still contain all $2^n$ rows; a star is an unspecified
output, not an omitted row. These conventions follow Hirahara, *NP-Hardness of
Learning Programs and Partial MCSP*, Definition 8.4 and the preceding paragraph:
https://eccc.weizmann.ac.il/report/2022/119/.

The separate unary size type preserves the $1^s$ component of that definition.
-/

@[expose] public section

namespace BooleanTruthTable

/-- All assignments, in lexicographic order with false before true. -/
def assignments : (n : ℕ) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n + 1 => (assignments n).map (Fin.cons false) ++
      (assignments n).map (Fin.cons true)

@[simp]
theorem length_assignments (n : ℕ) : (assignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [assignments, ih, pow_succ]; omega

theorem mem_assignments {n : ℕ} (v : Fin n → Bool) : v ∈ assignments n := by
  induction n with
  | zero =>
    have h : v = Fin.elim0 := funext fun i => Fin.elim0 i
    simp [assignments, h]
  | succ n ih =>
    have hv := Fin.cons_self_tail v
    cases h : v 0
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨Fin.tail v, ih _, by simpa [h] using hv⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨Fin.tail v, ih _, by simpa [h] using hv⟩

/-- The complete truth table of a Boolean function. -/
def ofFunction {n : ℕ} (f : (Fin n → Bool) → Bool) : List Bool :=
  (assignments n).map f

@[simp]
theorem length_ofFunction {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (ofFunction f).length = 2 ^ n := by
  simp [ofFunction]

theorem ofFunction_injective {n : ℕ} :
    Function.Injective (@ofFunction n) := by
  intro f g h
  funext v
  exact (List.map_inj_left.mp h) v (mem_assignments v)

/-- One entry of a partial truth table. -/
inductive PartialBit
  | value (b : Bool)
  | star
  deriving DecidableEq

namespace PartialBit

/-- A star places no constraint; a defined entry must be matched exactly. -/
def Agrees : PartialBit → Bool → Prop
  | value b, c => b = c
  | star, _ => True

instance (b : PartialBit) (c : Bool) : Decidable (b.Agrees c) := by
  cases b <;> unfold Agrees <;> infer_instance

/-- Two-bit tags: 00=false, 01=true, 10=star; 11 is rejected. -/
instance : BitstringEncoding PartialBit where
  encode
    | value b => [false, b]
    | star => [true, false]
  decode
    | [false, b] => some (value b)
    | [true, false] => some star
    | _ => none
  decode_encode b := by cases b <;> rfl

end PartialBit

/-- Pointwise agreement, including equality of the two table lengths. -/
def Agrees (observed : List PartialBit) (total : List Bool) : Prop :=
  List.Forall₂ PartialBit.Agrees observed total

instance (observed : List PartialBit) (total : List Bool) : Decidable (Agrees observed total) :=
  inferInstanceAs (Decidable (List.Forall₂ PartialBit.Agrees observed total))

theorem Agrees.length_eq {observed : List PartialBit} {total : List Bool}
    (h : Agrees observed total) : observed.length = total.length :=
  List.Forall₂.length_eq h

@[simp]
theorem agrees_values (a b : List Bool) :
    Agrees (a.map PartialBit.value) b ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [Agrees]
  | cons x xs ih =>
    cases b with
    | nil => simp [Agrees]
    | cons y ys =>
      simp only [Agrees, List.map_cons, List.forall₂_cons, PartialBit.Agrees,
        List.cons.injEq]
      exact and_congr Iff.rfl (ih ys)

/-- A size bound encoded in unary, not through the binary natural-number instance. -/
structure UnarySize where
  value : ℕ
  deriving DecidableEq

namespace UnarySize

instance : BitstringEncoding UnarySize where
  encode s := List.replicate s.value true
  decode bs := if bs.all id then some ⟨bs.length⟩ else none
  decode_encode s := by cases s; simp

@[simp]
theorem length_bitEncode (s : UnarySize) :
    (BitstringEncoding.bitEncode s).length = s.value := by
  exact List.length_replicate ..

end UnarySize

end BooleanTruthTable
