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

public import Mathlib.Computability.Encoding
public import Mathlib.Algebra.Field.Rat

/-!
# Bitstring encodings

This section provides a type`class`-inferrable version of
Mathlib's `Computability.Encoding`, specialized to the alphabet `Bool`.

Making it a `class` makes it easier to quickly ask if a function is computable in polynomial time,
without having to explicitly pass around the encoding (See `IsPolyTime`).

We set up instances for common types like Bool, ℕ, ℤ, ℚ,
and instance derivations for `Prod` and `List` types,
so that we obtain instances for many common types appearing in algorithms and complexity theory.

While different references may choose different encodings, generally our encodings should be
polytime-transcodable with any other reasonable binary encoding for a given type.
Thus, while it may not be obvious without further examination
which of several essentially equivalent encodings of a type is being used,
we can at least be sure that for functions between types with `BitstringEncoding` instances,
formalizations of questions of polynomial-time computability will capture the intended meaning.
-/

@[expose] public section

open Computability

section BitstringEncodings

/-- A canonical encoding of a type as bitstrings (`List Bool`).

This is a class version of Mathlib's `Computability.Encoding`, specialized to the
alphabet `Bool`. -/
class BitstringEncoding α extends Computability.Encoding α Bool

namespace BitstringEncoding

variable {α β : Type*}

/-- The encoding function of the canonical `BitstringEncoding` of `α`. -/
def bitEncode [BitstringEncoding α] (a : α) : List Bool := toEncoding.encode a

/-- The decoding function of the canonical `BitstringEncoding` of `α`. -/
def bitDecode [BitstringEncoding α] (l : List Bool) : Option α := toEncoding.decode l

/-- Decoding is a left inverse of encoding. -/
@[simp]
theorem bitDecode_bitEncode [BitstringEncoding α] (a : α) : bitDecode (bitEncode a) = some a :=
  toEncoding.decode_encode a

theorem bitEncode_injective [BitstringEncoding α] :
    Function.Injective (bitEncode : α → List Bool) :=
  (toEncoding (α := α)).encode_injective

/-- Transport a `BitstringEncoding` along an injection `f` with partial inverse `g`. -/
@[instance_reducible]
def ofLeftInverse [BitstringEncoding β] (f : α → β) (g : β → Option α)
    (h : ∀ x, g (f x) = some x) : BitstringEncoding α where
  encode a := bitEncode (f a)
  decode l := (bitDecode l).bind g
  decode_encode a := by simp [h]

/- ## Ground instances -/

/-- `ℕ` is encoded by its (little-endian) binary representation, as in
`Computability.encodeNat`. -/
instance : BitstringEncoding ℕ where
  encode := Computability.encodeNat
  decode l := some (Computability.decodeNat l)
  decode_encode n := congrArg some (Computability.decode_encodeNat n)

/-- `Bool` is encoded as a singleton bitstring. -/
instance : BitstringEncoding Bool where
  encode b := [b]
  decode l := match l with
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/- ## Self-delimiting blocks

To concatenate encodings of multipartite data structures,
we need each piece to announce its own end.
`delimit` writes each payload bit `b` as `true :: b :: ·` and terminates with `false`;
`undelimit` parses one such block off the front of the input. -/

/-- Make a bitstring self-delimiting: each payload bit `b` becomes the two bits
`[true, b]`, and the block is terminated by `false`. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- Parse one self-delimiting block from the front of the input, returning the payload
and the remaining input. -/
def undelimit : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: input => (undelimit input).map fun p => (b :: p.1, p.2)
  | _ => none

@[simp]
theorem undelimit_delimit (l rest : List Bool) :
    undelimit (delimit l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, undelimit, ih]

@[simp]
theorem length_delimit (l : List Bool) : (delimit l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, ih]; omega

/-- Parse a sequence of self-delimiting blocks, using `fuel` to bound the number of blocks.

This is the auxiliary, fuel-carrying implementation of `undelimitBlocks`; since every block
is nonempty, `input.length` is always enough fuel. -/
def undelimitBlocksAux : ℕ → List Bool → Option (List (List Bool))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, input =>
    -- `p.1` is the parsed block and `p.2` the remaining input; using projections rather than a
    -- pattern-matching lambda keeps the body free of matchers.
    (undelimit input).bind fun p => (undelimitBlocksAux fuel p.2).map (p.1 :: ·)

/-- Parse a sequence of self-delimiting blocks off the front of the input.

Since every block is nonempty, `input.length` bounds the number of blocks, so it always
suffices as fuel for `undelimitBlocksAux`. -/
def undelimitBlocks (input : List Bool) : Option (List (List Bool)) :=
  undelimitBlocksAux input.length input

theorem length_le_length_flatten_delimit (l : List (List Bool)) :
    l.length ≤ ((l.map delimit).flatten).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      length_delimit]
    omega

private theorem undelimitBlocksAux_flatten_delimit (l : List (List Bool)) (fuel : ℕ)
    (hfuel : l.length ≤ fuel) : undelimitBlocksAux fuel ((l.map delimit).flatten) = some l := by
  induction l generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons b t ih =>
    rw [List.length_cons] at hfuel
    cases fuel <;> cases b <;> grind [delimit, undelimitBlocksAux, undelimit_delimit]

theorem undelimitBlocks_flatten_delimit (l : List (List Bool)) :
    undelimitBlocks ((l.map delimit).flatten) = some l :=
  undelimitBlocksAux_flatten_delimit l _ (length_le_length_flatten_delimit l)

@[simp]
theorem mapM_bitDecode_map_bitEncode [BitstringEncoding α] (l : List α) :
    (l.map bitEncode).mapM bitDecode = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/- ## Derived instances -/

/-- A pair is encoded as a self-delimiting block for the first component followed by the
encoding of the second. -/
instance [BitstringEncoding α] [BitstringEncoding β] : BitstringEncoding (α × β) where
  encode p := delimit (bitEncode p.1) ++ bitEncode p.2
  decode input :=
    match undelimit input with
    | none => none
    | some (block, rest) =>
      match bitDecode block, bitDecode rest with
      | some a, some b => some (a, b)
      | _, _ => none
  decode_encode p := by simp

/-- A list is encoded as the concatenation of self-delimiting blocks for its elements. -/
instance [BitstringEncoding α] : BitstringEncoding (List α) where
  encode l := ((l.map bitEncode).map delimit).flatten
  decode input := (undelimitBlocks input).bind (·.mapM bitDecode)
  decode_encode l := by
    rw [undelimitBlocks_flatten_delimit (l.map bitEncode)]
    exact mapM_bitDecode_map_bitEncode l

/-- A subtype inherits the encoding of the ambient type; decoding additionally checks the
defining predicate. -/
@[instance_reducible]
def ofSubtype {p : α → Prop} [BitstringEncoding α] [DecidablePred p] :
    BitstringEncoding (Subtype p) where
  encode x := bitEncode x.val
  decode input := (bitDecode input).bind fun a => if h : p a then some ⟨a, h⟩ else none
  decode_encode x := by simp [x.property]

/-- `ℕ+` is encoded as the subtype `{n : ℕ // 0 < n}` it is defined to be. -/
instance : BitstringEncoding ℕ+ :=
  ofSubtype (p := fun n : ℕ => 0 < n)

/-- `ℤ` is encoded via the pair `(n.toNat, (-n).toNat)` (one component is always `0`). -/
instance : BitstringEncoding ℤ :=
  ofLeftInverse (fun n : ℤ => (n.toNat, (-n).toNat))
    (fun p => some ((p.1 : ℤ) - (p.2 : ℤ))) (fun n => congrArg some (by dsimp only; omega))

/-- `ℚ` is encoded as its (reduced) numerator-denominator pair. -/
instance : BitstringEncoding ℚ :=
  ofLeftInverse (fun q : ℚ => (q.num, q.den))
    (fun p => some ((p.1 : ℚ) / (p.2 : ℚ))) (fun q => by simp [Rat.num_div_den])

end BitstringEncoding

end BitstringEncodings
