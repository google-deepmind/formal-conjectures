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
public import Mathlib.Computability.TuringMachine.Computable

/-!
# Complexity Classes

This file contains formal definitions of notions from complexity theory,
including the complexity classes P, NP, and coNP.

*References:*
- Sanjeev Arora and Boaz Barak. Computational Complexity: A Modern Approach.
  Cambridge University Press, 2009.
-/

@[expose] public section

open Computability Turing

namespace ComplexityTheory

/--
The type of decision problems.

We define these as functions from lists of booleans to booleans,
implicitly assuming the usual encodings.
-/
abbrev DecisionProblem := List Bool → Bool

/--
The type of complexity classes. We define these as sets of decision problems.
-/
abbrev ComplexityClass := Set DecisionProblem

/--
`IsPolyTimeWithEncoding ea eb f` asserts that `f` is computable in polynomial time
when its input and output are encoded via the given `Encoding`s `ea` and `eb`.
-/
def IsPolyTimeWithEncoding {α β Γα Γβ : Type} (ea : Encoding α Γα) (eb : Encoding β Γβ)
    (f : α → β) :=
  Nonempty (TM2ComputableInPolyTime ea.encode eb.encode f)

/--
A function is polynomial-time computable when it is `IsPolyTimeWithEncoding`
for the canonical `Bool`-alphabet encodings of its domain and codomain
as given by the `BitstringEncoding` typeclass.
-/
def IsPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (f : α → β) : Prop :=
  IsPolyTimeWithEncoding (BitstringEncoding.toEncoding (α := α)) (BitstringEncoding.toEncoding (α := β)) f

/-- The identity function is polynomial-time computable. -/
theorem isPolyTime_id {α : Type} [BitstringEncoding α] : IsPolyTime (id : α → α) :=
  ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩

/- ## Class definitions -/

/--
The class P is the set of decision problems
decidable in polynomial time by a deterministic Turing machine.
-/
def P : ComplexityClass :=
  { L | IsPolyTime L }

/--
The class NP is the set of decision problems
such that there exists a polynomial `p` over ℕ and a poly-time Turing machine
where for all `x`, `L x = true` iff there exists a `w` of length at most `p (|x|)`
such that the Turing machine accepts the pair `(x,w)`.

See Definition 2.1 in Arora-Barak (2009).
-/
def NP : ComplexityClass :=
  { L | ∃ (p : Polynomial ℕ), ∃ R : (List Bool × List Bool) → Bool,
      IsPolyTime R ∧
      ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ R (x, w) }

/--
The class coNP is the set of decision problems
whose complements are in NP.
-/
def coNP : ComplexityClass :=
  { L | Lᶜ ∈ NP }

end ComplexityTheory
