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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice

/-!
# Hypergraph Ramsey Numbers

This file defines the `r`-uniform hypergraph Ramsey number `R_r(n)`.
-/


namespace Combinatorics

/--
The `r`-uniform hypergraph Ramsey number `R_r(n)`.
The smallest natural number `m` such that every 2-coloring of the `r`-subsets of a set of size `m`
contains a monochromatic subset of size `n`.
-/
noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf { m | ∀ (c : Finset (Fin m) → Bool),
    ∃ (S : Finset (Fin m)), S.card = n ∧
      ∃ (color : Bool), ∀ (e : Finset (Fin m)), e ⊆ S → e.card = r → c e = color }

end Combinatorics
