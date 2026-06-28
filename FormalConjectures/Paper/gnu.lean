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

import FormalConjectures.Util.ProblemImports

/-!
# This file defines the number of non-isomorphic finite groups of order `n` (OEIS A000001)
-/

namespace GroupNumberFunction

/--
Objects of the category `Grp` that have (extended) cardinality equal to `n`.
We use `ENat.card` because the more usual `Nat.card` is defined as 0 for infinite arguments,
so it would yield the wrong count for order 0.
-/
abbrev GrpOfOrder (n : ℕ) := {G : GrpCat.{0} // ENat.card G = n}

/--
Two groups are related if they are isomorphic in the category `Grp`.
-/
def FiniteGrpSetoid (n : ℕ) : Setoid (GrpOfOrder n) where
  r := fun ⟨g1, _⟩ ⟨g2, _⟩ => Nonempty (g1 ≅ g2)
  iseqv := {
    refl := fun ⟨X, _⟩  => ⟨CategoryTheory.Iso.refl X⟩
    symm := fun ⟨a⟩ => ⟨a.symm⟩
    trans := fun ⟨a⟩ ⟨b⟩ => ⟨a.trans b⟩
  }

/--
Classes of isomorphism of groups of order `n`.
-/
def NonIsoFiniteGrp (n : ℕ) := Quotient (FiniteGrpSetoid n)

/--
The number of non-isomorphic finite groups of order `n`.

Equivalently, the OEIS sequence A000001, with gnu 0 = 0, gnu 1 = gnu 2 = gnu 3 = 1, gnu 4 = 2, etc.
-/
noncomputable def gnu (n : ℕ) : ℕ := Nat.card (NonIsoFiniteGrp n)

end GroupNumberFunction
