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

public import FormalConjecturesForMathlib.Computability.Circuit
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Card

/-!
# One-way functions against nonuniform circuits

The forward function is uniformly polynomial-time computable and preserves length.
Inversion must find any preimage, and success is measured on the image of a uniformly
random input. Adversaries are arbitrary polynomial-size $B_2$ circuits.
Randomized circuit adversaries are covered by fixing their random coins.

*Reference:* Oded Goldreich, *Foundations of Cryptography, Volume 1: Basic Tools*,
Cambridge University Press, 2001, Sections 2.2.3 and 2.2.5.
The [author's Chapter 2 draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part2.pdf)
contains the length-preserving convention and Definition 2.6 for nonuniform one-way functions.
-/

@[expose] public section

namespace ComplexityTheory

open Cslib.Circuits Filter

/-- A length-preserving map on Boolean words, indexed by their length. -/
abbrev LengthPreservingFamily := (n : ℕ) → (Fin n → Bool) → (Fin n → Bool)

/-- Apply a length-preserving family to a list of bits. -/
def LengthPreservingFamily.onList (f : LengthPreservingFamily) (x : List Bool) : List Bool :=
  List.ofFn (f x.length x.get)

@[simp] theorem LengthPreservingFamily.onList_length (f : LengthPreservingFamily) (x : List Bool) :
    (f.onList x).length = x.length := by
  simp [LengthPreservingFamily.onList]

/-- One finite-state, binary multitape machine computes the function in time polynomial
in the input length. -/
def PolynomialTime (f : List Bool → List Bool) : Prop :=
  ∃ a k : ℕ, 0 < a ∧ ∃ space,
    Turing.MultiTapeTM.ComputableInTimeAndSpace f (.refl _) (.refl _)
      (fun x => a * (x.length + 1) ^ k) space

/-- Count the inputs for which the circuit finds a preimage of the forward output. -/
noncomputable def inversionSuccesses (f : LengthPreservingFamily) {n g : ℕ}
    (c : Circuit binarySignature n g n) : ℕ := by
  classical
  exact (Finset.univ.filter fun x =>
    f n (c.eval binaryInterpretation (f n x)) = f n x).card

@[simp] theorem inversionSuccesses_id (n : ℕ) :
    inversionSuccesses (fun _ x => x) (Circuit.id binarySignature n) = 2 ^ n := by
  simp [inversionSuccesses]

@[simp] theorem inversionSuccesses_const (v : (n : ℕ) → Fin n → Bool) {n g : ℕ}
    (c : Circuit binarySignature n g n) :
    inversionSuccesses (fun n _ => v n) c = 2 ^ n := by
  simp [inversionSuccesses]

/-- A uniformly computable function is nonuniformly one-way if, for every polynomial gate
bound and every $b$, all sufficiently long inputs give inversion probability at most $n^{-b}$.
The finite count expresses this bound without division. Quantifying over every exponent
also absorbs multiplicative constants in the negligible bound. -/
def OneWay (f : LengthPreservingFamily) : Prop :=
  PolynomialTime f.onList ∧
    ∀ a k b : ℕ, ∀ᶠ n in atTop, ∀ g (c : Circuit binarySignature n g n),
      g ≤ a * n ^ k → n ^ b * inversionSuccesses f c ≤ 2 ^ n

end ComplexityTheory
