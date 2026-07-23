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

public import Mathlib.Computability.Encoding
public import FormalConjecturesForMathlib.Computability.Encoding

@[expose] public section

open Computability

namespace ComplexityTheory

/-!
# Encodings for Natural Numbers
This section provides `FinEncoding` instances to encode `ℕ`, `List ℕ`, and related
types into `List Bool`. This is required to define the complexity of problems
where the inputs are natural numbers (e.g. integer factorization).
-/

/-- Encodes a natural number into a list of booleans (e.g., binary representation). -/
def natToBits (n : ℕ) : List Bool := sorry

/-- Decodes a list of booleans back into a natural number. -/
def bitsToNat (l : List Bool) : ℕ := sorry

@[simp]
lemma bitsToNat_natToBits (n : ℕ) : bitsToNat (natToBits n) = n := sorry

/-- A boolean encoding for single natural numbers. -/
def finEncodingNat : Computability.FinEncoding ℕ where
  Γ := Bool
  encode := natToBits
  decode := Option.some ∘ bitsToNat
  decode_encode := by
    intro n
    simp [bitsToNat_natToBits]
  ΓFin := Bool.fintype

/-- Prefix-free encoding of a list of natural numbers into `List Bool`.
    A standard way is to double the bits of each number and use `01` as a separator. -/
def encodeListNat (l : List ℕ) : List Bool := sorry

/-- Decodes a prefix-free boolean string back into a list of natural numbers. -/
def decodeListNat (l : List Bool) : Option (List ℕ) := sorry

@[simp]
lemma decode_encodeListNat (l : List ℕ) : decodeListNat (encodeListNat l) = some l := sorry

/-- A boolean encoding for lists of natural numbers. -/
def finEncodingListNat : Computability.FinEncoding (List ℕ) where
  Γ := Bool
  encode := encodeListNat
  decode := decodeListNat
  decode_encode := decode_encodeListNat
  ΓFin := Bool.fintype

/-- A boolean encoding for pairs of natural numbers. -/
def finEncodingNatProdNat : Computability.FinEncoding (ℕ × ℕ) where
  Γ := Bool
  encode := fun ⟨n1, n2⟩ => encodeListNat [n1, n2]
  decode := fun l => match decodeListNat l with
    | some [n1, n2] => some (n1, n2)
    | _ => none
  decode_encode := by
    intro ⟨n1, n2⟩
    simp [decode_encodeListNat]
  ΓFin := Bool.fintype

/-- A boolean encoding for 4-tuples of natural numbers (used for discrete log). -/
def finEncodingNat4 : Computability.FinEncoding (ℕ × ℕ × ℕ × ℕ) where
  Γ := Bool
  encode := fun ⟨n1, n2, n3, n4⟩ => encodeListNat [n1, n2, n3, n4]
  decode := fun l => match decodeListNat l with
    | some [n1, n2, n3, n4] => some (n1, n2, n3, n4)
    | _ => none
  decode_encode := by
    intro ⟨n1, n2, n3, n4⟩
    simp [decode_encodeListNat]
  ΓFin := Bool.fintype

/-- A boolean encoding for pairs of `List ℕ` and `ℕ` (used for square-root sum). -/
def finEncodingListNatProdNat : Computability.FinEncoding (List ℕ × ℕ) where
  Γ := Bool
  encode := fun ⟨L, n⟩ => encodeListNat (n :: L)
  decode := fun l => match decodeListNat l with
    | some (n :: L) => some (L, n)
    | _ => none
  decode_encode := by
    intro ⟨L, n⟩
    simp [decode_encodeListNat]
  ΓFin := Bool.fintype

end ComplexityTheory
