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
public import Mathlib.Computability.TMComputable

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
when its input and output are encoded via the given `FinEncoding`s `ea` and `eb`.
-/
def IsPolyTimeWithEncoding {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) :=
  Nonempty (TM2ComputableInPolyTime ea eb f)

/--
A function is polynomial-time computable when it is `IsPolyTimeWithEncoding`
for the canonical `Bool`-alphabet encodings of its domain and codomain
as given by the `BitstringEncoding` typeclass.
-/
def IsPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (f : α → β) : Prop :=
  IsPolyTimeWithEncoding (BitstringEncoding.toFinEncoding α) (BitstringEncoding.toFinEncoding β) f

end ComplexityTheory
