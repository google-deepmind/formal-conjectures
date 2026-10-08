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

public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.ModelTheory.Encoding
public import Mathlib.ModelTheory.Order

/-!
# Gödel numberings of first-order formulas

Mathlib encodes the terms and the bounded formulas of a first-order language `L` as lists of
symbols (`FirstOrder.Language.Term.listEncode` and
`FirstOrder.Language.BoundedFormula.listEncode`), and derives from this an `Encodable`
instance on terms. This file derives `Encodable` instances on bounded formulas, formulas and
sentences in the same way. Given `Encodable` instances on the function symbols
`Σ n, L.Functions n` and on the relation symbols `Σ n, L.Relations n`, every sentence `φ` of
`L` gets a Gödel number `Encodable.encode φ : ℕ`.

The file also provides `Encodable` instances on the symbols of `Language.ring`,
`Language.order`, and of sums of languages.

## Main declarations

- `FirstOrder.Language.BoundedFormula.encodableSigma`: Gödel numbering of
  `Σ n, L.BoundedFormula α n`.
- `FirstOrder.Language.BoundedFormula.encodable`: Gödel numbering of `L.BoundedFormula α n`,
  hence of `L.Formula α` and `L.Sentence`.

## Implementation notes

The numbering is the composition of Mathlib's list encoding of formulas with Mathlib's
`Encodable` instance on lists and the given encodings of the symbols, so it is effective in the
usual informal sense. For a language with finitely many symbols, any two injective encodings of
the symbols yield Gödel numberings that are computably inter-translatable, so notions such as
decidability of a theory do not depend on the choice made here. No `Primcodable` instance is
provided; computability statements about theories are phrased on `ℕ` through `Encodable.encode`.
-/

@[expose] public section

namespace FirstOrder.Language

open Encodable

variable {L : Language} {α : Type*}

section Symbols

/-- The function symbols of a sum of two languages are encodable when those of both summands
are. -/
instance sum.encodableFunctions {L' : Language} [Encodable (Σ n, L.Functions n)]
    [Encodable (Σ n, L'.Functions n)] : Encodable (Σ n, (L.sum L').Functions n) :=
  ofEquiv _ (Equiv.sigmaSumDistrib L.Functions L'.Functions)

/-- The relation symbols of a sum of two languages are encodable when those of both summands
are. -/
instance sum.encodableRelations {L' : Language} [Encodable (Σ n, L.Relations n)]
    [Encodable (Σ n, L'.Relations n)] : Encodable (Σ n, (L.sum L').Relations n) :=
  ofEquiv _ (Equiv.sigmaSumDistrib L.Relations L'.Relations)

/-- A relational language has no function symbols. -/
instance IsRelational.encodableFunctions [L.IsRelational] : Encodable (Σ n, L.Functions n) :=
  ⟨fun f => isEmptyElim f.2, fun _ => none, fun f => isEmptyElim f.2⟩

/-- An algebraic language has no relation symbols. -/
instance IsAlgebraic.encodableRelations [L.IsAlgebraic] : Encodable (Σ n, L.Relations n) :=
  ⟨fun r => isEmptyElim r.2, fun _ => none, fun r => isEmptyElim r.2⟩

/-- The function symbols `+`, `*`, `-`, `0`, `1` of the language of rings are encoded as
`0`, `1`, `2`, `3`, `4`. -/
instance ring.encodableFunctions : Encodable (Σ n, Language.ring.Functions n) :=
  ofLeftInjection
    (fun f => match f with
      | ⟨_, .add⟩ => 0
      | ⟨_, .mul⟩ => 1
      | ⟨_, .neg⟩ => 2
      | ⟨_, .zero⟩ => 3
      | ⟨_, .one⟩ => 4)
    (fun n => match n with
      | 0 => some ⟨2, Ring.addFunc⟩
      | 1 => some ⟨2, Ring.mulFunc⟩
      | 2 => some ⟨1, Ring.negFunc⟩
      | 3 => some ⟨0, Ring.zeroFunc⟩
      | 4 => some ⟨0, Ring.oneFunc⟩
      | _ => none)
    (fun f => by rcases f with ⟨_, f⟩; cases f <;> rfl)

/-- The unique relation symbol `≤` of the language of orders is encoded as `0`. -/
instance order.encodableRelations : Encodable (Σ n, Language.order.Relations n) :=
  ofLeftInjection (fun _ => (0 : ℕ)) (fun _ => some default) fun _ =>
    congrArg some (Subsingleton.elim _ _)

end Symbols

namespace BoundedFormula

variable [Encodable α] [Encodable (Σ n, L.Functions n)] [Encodable (Σ n, L.Relations n)]

/-- The Gödel numbering of bounded formulas, obtained from the list encoding
`BoundedFormula.encoding` and the `Encodable` instances on lists and on the symbols. -/
instance encodableSigma : Encodable (Σ n, L.BoundedFormula α n) :=
  ofLeftInjection BoundedFormula.encoding.encode BoundedFormula.encoding.decode
    BoundedFormula.encoding.decode_encode

/-- The Gödel numbering of bounded formulas with `n` bound variables, and in particular of
formulas (`n = 0`) and sentences (`n = 0` and `α = Empty`). -/
instance encodable (n : ℕ) : Encodable (L.BoundedFormula α n) :=
  ofLeftInjection (fun φ => (⟨n, φ⟩ : Σ n, L.BoundedFormula α n))
    (fun ψ => if h : ψ.1 = n then some (h ▸ ψ.2) else none) fun _ => dif_pos rfl

end BoundedFormula

end FirstOrder.Language
