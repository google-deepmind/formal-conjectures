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
import Mathlib.Order.CompletePartialOrder
import Mathlib.SetTheory.Ordinal.Exponential

open Cardinal Ordinal

universe u

/--
This proposition asserts the Ramsey property `κ → (κ, c)₂`, where `κ` is the
cardinality of the ordinal `ω ^ β`.

It states that for any 2-coloring of the edges of a complete graph on `κ`
vertices, there must be a monochromatic red clique of size `κ` or a
monochromatic blue clique of size `c`.
-/
def OmegaPowerRamsey  (β : Ordinal.{u}) (c : Cardinal.{u}): Prop :=
  -- Let α be the ordinal ω^β
  let κ := ω ^ β
  -- Let V be a type with the cardinality of α.
  let V := κ.toType
  -- For any red/blue edge coloring of the complete graph on V...
  -- (represented by two graphs G_red and G_blue that are complements)
  ∀ (G_red G_blue : SimpleGraph V), IsCompl G_red G_blue →
    -- ...there is either a red K_α
    (∃ (s : Set V), G_red.IsClique s ∧ #s = κ.card) ∨
    -- ...or there is a blue K_3.
    (∃ (s : Set V), G_blue.IsClique s ∧ #s = c)
