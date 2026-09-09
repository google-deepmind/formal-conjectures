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
public import FormalConjecturesForMathlib.Computability.ClockedEvaluation
public import FormalConjecturesForMathlib.Computability.FiniteTests

/-!
# Encoded clocked descriptions and exhaustive enumeration

Reuse the repository's binary natural-number and self-delimiting pair encodings. A description
contains code, coefficient, and exponent; all three contribute to its encoded length.
Canonical decoding rejects aliases as well as invalid descriptions. Code semantics are supplied
separately: this module does not identify the code type with a polynomial-time machine model.
-/

@[expose] public section

namespace Computability.FiniteTests

open BitstringEncoding ClockedEvaluation

variable {α : Type} [BitstringEncoding α]

/-- Decode only the canonical encoding of an object. -/
def decodeCanonical (bits : List Bool) : Option α :=
  (bitDecode bits).filter fun a ↦ bitEncode a == bits

@[simp]
theorem decodeCanonical_eq_some {bits : List Bool} {a : α} :
    decodeCanonical bits = some a ↔ bitEncode a = bits := by
  constructor
  · intro h
    simpa [decodeCanonical] using (Option.filter_eq_some_iff.mp h).2
  · rintro rfl
    simp [decodeCanonical]

/-- Every canonical code of length at most the bound, with no missing valid candidates. -/
def Enumeration.ofBitstringEncoding : Enumeration α where
  size a := (bitEncode a).length
  upTo n := (Enumeration.bitstringsUpTo n).filterMap decodeCanonical (by
    intro b b' a ha ha'
    have h : bitEncode a = b := decodeCanonical_eq_some.mp ha
    have h' : bitEncode a = b' := decodeCanonical_eq_some.mp ha'
    exact h.symm.trans h')
  mem_upTo := by
    intro a n
    simp only [Finset.mem_filterMap, Enumeration.mem_bitstringsUpTo, decodeCanonical_eq_some]
    constructor
    · rintro ⟨bits, hb, rfl⟩
      exact hb
    · intro h
      exact ⟨bitEncode a, h, rfl⟩

/-- A finite code together with its explicit polynomial clock. -/
structure ClockedCode (α : Type) where
  code : α
  clock : Clock
  deriving DecidableEq

instance : BitstringEncoding (ClockedCode α) :=
  BitstringEncoding.ofLeftInverse
    (fun a ↦ (a.code, a.clock.coefficient, a.clock.exponent))
    (fun p ↦ (Clock.ofNat p.2.1 p.2.2).map fun clock ↦ ⟨p.1, clock⟩)
    (fun a ↦ by simp)

/-- The exact encoded length accounts for both clock parameters and the underlying code. -/
theorem ClockedCode.encoded_length (a : ClockedCode α) :
    (bitEncode a).length =
      2 * (bitEncode a.code).length + 1 +
        (2 * (bitEncode a.clock.coefficient).length + 1 +
          (bitEncode a.clock.exponent).length) := by
  change (delimit (bitEncode a.code) ++
    (delimit (bitEncode a.clock.coefficient) ++ bitEncode a.clock.exponent)).length = _
  simp only [List.length_append, length_delimit]

end Computability.FiniteTests
