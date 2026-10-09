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

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
# Group Number Function

This file defines `groupNumber n`, the number of non-isomorphic finite groups of order $n$.
This is the OEIS sequence [A000001](https://oeis.org/A000001), sometimes denoted $\mathrm{gnu}(n)$
(the "group number") in the literature.
-/

namespace GroupNumberFunction

/--
Objects of the category $\mathrm{Grp}$ that have (extended) cardinality equal to $n$.
We use `ENat.card` because the more usual `Nat.card` is defined to be $0$ for infinite
arguments, so it would yield the wrong count for order $0$.
-/
abbrev GrpOfOrder (n : ℕ) := {G : GrpCat.{0} // ENat.card G = n}

/--
Two groups are related if they are isomorphic in the category $\mathrm{Grp}$.
-/
def FiniteGrpSetoid (n : ℕ) : Setoid (GrpOfOrder n) where
  r := fun ⟨g1, _⟩ ⟨g2, _⟩ => Nonempty (g1 ≅ g2)
  iseqv := {
    refl := fun ⟨X, _⟩  => ⟨CategoryTheory.Iso.refl X⟩
    symm := fun ⟨a⟩ => ⟨a.symm⟩
    trans := fun ⟨a⟩ ⟨b⟩ => ⟨a.trans b⟩
  }

/--
Isomorphism classes of groups of order $n$.
-/
def NonIsoFiniteGrp (n : ℕ) := Quotient (FiniteGrpSetoid n)

/--
The number of non-isomorphic finite groups of order $n$, denoted $\mathrm{gnu}(n)$ in
the literature.

Equivalently this is the OEIS sequence [A000001](https://oeis.org/A000001), with
`groupNumber 0 = 0`, `groupNumber 1 = groupNumber 2 = groupNumber 3 = 1`,
`groupNumber 4 = 2`, etc.
-/
noncomputable def groupNumber (n : ℕ) : ℕ := Nat.card (NonIsoFiniteGrp n)

end GroupNumberFunction
