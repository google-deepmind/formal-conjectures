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
# P vs NP

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/P_versus_NP_problem)
Computational Complexity: A Modern Approach by Arora and Barak, 2009.
TODO (add additional ref information)
-/

open Computability Turing

namespace PvsNP

/--
A simple definition to abstract the notion of a poly-time Turing machine into a predicate.
-/
def isComputableInPolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
  (f : α → β) := Nonempty (TM2ComputableInPolyTime ea eb f)

/--
The type of complexity classes over an alphabet `α` consists of sets of languages over `α`.
-/
abbrev ComplexityClass (α : Type) := Set (Language α)

/--
Given a finEncoding of a type `α`, we can get a finEncoding of `List α`
-/
def listFinEncoding {α : Type} (ea : FinEncoding α) : FinEncoding (List α) := sorry

/--
This function courtesy of Daniel Weber,
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Formalise.20the.20proposition.20P.20.E2.89.A0NP/with/453031558
-/
def pairFinEncoding {α β : Type*} (ea : FinEncoding α) (eb : FinEncoding β) :
    Computability.FinEncoding (α × β) where
  /- The encoding language is the direct sum of the respective encoding languages -/
  Γ := ea.Γ ⊕ eb.Γ
  /- The encoding function is to concatenate the encodings -/
  encode x := (ea.encode x.1).map .inl ++ (eb.encode x.2).map .inr
  /- The decoding function is to filter symbols by the encoding languages they correspond to
  and decode the parts separately. -/
  decode x := Option.map₂ Prod.mk (ea.decode (x.filterMap Sum.getLeft?))
                                  (eb.decode (x.filterMap Sum.getRight?))
  decode_encode x := by
    simp [List.filterMap_append, ea.decode_encode, eb.decode_encode]
    sorry
  ΓFin := inferInstance

/--
The class P is the set of languages over an alphabet `α`
decidable in polynomial time by a deterministic Turing machine
-/
def P {α : Type} [Nontrivial α] [Finite α] (ea : FinEncoding α) : ComplexityClass α :=
  { L | isComputableInPolyTime
          (listFinEncoding ea)
          (Computability.finEncodingBoolBool)
          (fun x => L x = true) }

/--
The class NP is the set of languages over an alphabet `α`
such that there exists a polynomial over ℕ and a poly-time Turing machine
where for all `x`, `L x = true` iff there exists a `w` of length at most `p (length x)`
such that the Turing machine accepts the pair `(x,w)`.
-/
def NP {α : Type} [Nontrivial α] [Finite α] (ea : FinEncoding α) : ComplexityClass α :=
  { L | ∃ (p : ℕ → ℕ), ∃ R : (List α × List Bool) → Bool,
      isComputableInPolyTime
        (pairFinEncoding (listFinEncoding ea) ((listFinEncoding Computability.finEncodingBoolBool)))
        (Computability.finEncodingBoolBool)
        (R) ∧
      ∀ x, L x = true ↔ ∃ w : List Bool, w.length ≤ p (x.length) ∧ R (x, w) = true

   }

@[category research open, AMS 68]
theorem P_ne_NP (α : Type) [Nontrivial α] [Finite α] (ea : FinEncoding α) :
    P ea ≠ NP ea := by
  sorry

@[category undergraduate, AMS 68]
theorem P_subset_NP (α : Type) [Nontrivial α] [Finite α] (ea : FinEncoding α) :
    P ea ⊆ NP ea := by
  sorry

end PvsNP
