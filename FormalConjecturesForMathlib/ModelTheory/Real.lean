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

public import FormalConjecturesForMathlib.ModelTheory.Encoding
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Expansions of the real field

This file makes `ℝ` a structure for the language of rings and for the language of orders. It
defines the language `Language.exp` with a single unary function symbol `exp`, the language
`Language.orderedExpField` of ordered exponential fields, and the *real exponential field*
`(ℝ, +, *, -, 0, 1, ≤, exp)` as a structure for that language.

## Main declarations

- `FirstOrder.Language.exp`: the language with one unary function symbol `exp`.
- `FirstOrder.Language.orderedExpField`: the language of ordered exponential fields.

## Implementation notes

Mathlib deliberately does not make `Ring.compatibleRingOfRing` or `orderStructure` instances,
because for a general type `R` the round trip `Ring R → Language.ring.Structure R → Ring R`
need not commute definitionally. Here they are declared as instances for the single type `ℝ`.
Mathlib has no instance producing a `Ring` or `LE` structure from a first-order structure on a
concrete type, so no such round trip arises.
-/

@[expose] public section

namespace FirstOrder

/-- The type of function symbols of `Language.exp`: a single unary symbol `exp`. -/
inductive expFunc : ℕ → Type
  | exp : expFunc 1
  deriving DecidableEq

namespace Language

/-- The language with a single unary function symbol `exp` and no relation symbols. -/
protected def exp : Language := ⟨expFunc, fun _ => Empty⟩
  deriving IsAlgebraic

/-- The language of ordered exponential fields: the language of rings, together with a unary
function symbol `exp` and the order relation `≤`. -/
protected abbrev orderedExpField : Language :=
  Language.ring.sum (Language.exp.sum Language.order)

/-- The language of ordered exponential fields contains the order symbol `≤`. -/
instance orderedExpField.instIsOrdered : Language.orderedExpField.IsOrdered :=
  ⟨Sum.inr leSymb⟩

/-- The function symbol `exp` is encoded as `0`. -/
instance exp.encodableFunctions : Encodable (Σ n, Language.exp.Functions n) :=
  Encodable.ofLeftInjection (fun _ => (0 : ℕ)) (fun _ => some ⟨1, expFunc.exp⟩) fun f => by
    rcases f with ⟨_, f⟩
    cases f
    rfl

noncomputable section Real

/-- `ℝ` as a structure for the language of rings, with the usual ring operations. -/
instance compatibleRingReal : Ring.CompatibleRing ℝ := Ring.compatibleRingOfRing ℝ

/-- `ℝ` as a structure for the language of orders, with `≤` interpreted as `≤`. -/
instance orderStructureReal : Language.order.Structure ℝ := orderStructure ℝ

instance orderOrderedStructureReal : Language.order.OrderedStructure ℝ := ⟨fun _ => Iff.rfl⟩

/-- `ℝ` as a structure for `Language.exp`, with `exp` interpreted as the exponential function. -/
instance expStructureReal : Language.exp.Structure ℝ where
  funMap {n} f := match n, f with
    | _, .exp => fun x => Real.exp (x 0)

@[simp]
theorem funMap_exp (x : Fin 1 → ℝ) :
    Structure.funMap (L := Language.exp) expFunc.exp x = Real.exp (x 0) :=
  rfl

/-- In the real exponential field, `≤` is interpreted as `≤`. -/
instance orderedExpFieldOrderedStructureReal : Language.orderedExpField.OrderedStructure ℝ :=
  ⟨fun _ => Iff.rfl⟩

-- In the real exponential field, the symbol `exp` is interpreted as the exponential function.
example (x : ℝ) :
    Structure.funMap (L := Language.orderedExpField) (Sum.inr (Sum.inl expFunc.exp)) ![x] =
      Real.exp x :=
  rfl

-- In the real exponential field, the symbol `+` is interpreted as addition.
example (x y : ℝ) :
    Structure.funMap (L := Language.orderedExpField) (Sum.inl Ring.addFunc) ![x, y] = x + y :=
  rfl

-- In the real exponential field, the symbol `≤` is interpreted as the order of `ℝ`.
example (x y : ℝ) :
    Structure.RelMap (L := Language.orderedExpField) leSymb ![x, y] ↔ x ≤ y :=
  Iff.rfl

-- The Gödel numbering of sentences of `Language.orderedExpField` is found by instance resolution.
example : Encodable Language.orderedExpField.Sentence := inferInstance

end Real

end Language

end FirstOrder
