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
import FormalConjectures.Util.ProblemImports

/-!
# Conjectures in Complexity Theory

This file contains formal statements of some of the basic definitions in complexity theory,
including `DecisionProblem`s, `ComplexityClass`es, `P`, `NP`, and `coNP`.

*References:*
- Arora, Sanjeev, and Boaz Barak. Computational complexity: a modern approach.
  Cambridge University Press, 2009.
-/

open Computability Turing

namespace ComplexityTheory

/--
The type of decision problems.

We define these as functions from lists of booleans to booleans,
implictly assuming the usual encodings.
-/
abbrev DecisionProblem := List Bool → Bool

/--
The type of complexity classes. We define these as sets of decision problems.
-/
abbrev ComplexityClass := Set DecisionProblem

/--
`IsPolyTimeWithEncoding ea eb f` asserts that `f` is computable in polynomial time when its
input and output are encoded via the given `FinEncoding`s `ea` and `eb`.
-/
def IsPolyTimeWithEncoding {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) :=
  Nonempty (TM2ComputableInPolyTime ea eb f)

/--
A function between `BitstringEncoding` types is **polynomial-time computable** when it is
`IsPolyTimeWithEncoding` for the canonical `Bool`-alphabet encodings of its domain and
codomain. Keeping the encodings implicit lets complexity-theoretic statements be written
succinctly, e.g. "integer factorization is in P" is literally `IsPolyTime Nat.primeFactorsList`.

(Mathlib's `TM2ComputableInPolyTime` is restricted to `Type 0`, so this is too.)
-/
def IsPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (f : α → β) : Prop :=
  IsPolyTimeWithEncoding (BitstringEncoding.toFinEncoding α) (BitstringEncoding.toFinEncoding β) f

/-- Sanity check: the identity function is polynomial-time computable. -/
theorem isPolyTime_id {α : Type} [BitstringEncoding α] : IsPolyTime (id : α → α) :=
  ⟨Turing.idComputableInPolyTime (BitstringEncoding.toFinEncoding α)⟩

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
