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

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.SetTheory.Ordinal.Exponential

open Cardinal Ordinal

universe u

/--
This proposition asserts the ordinal Ramsey property `α → (β, c)²`.

It states that for any 2-coloring of the complete graph on the ordinal `α`,
one of the following must hold:
* There is a red clique which is order-isomorphic to `β`.
* There is a blue clique of cardinality `c`.
-/
def OrdinalCardinalRamsey (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  -- For any 2-coloring of `α`,
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    -- either there is a red `K_β`
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
   -- or there is a blue `K_c`.
    ∃ s, blue.IsClique s ∧ #s = c
