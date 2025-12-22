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
This proposition asserts the ordinal Ramsey property `ω^β → (ω^β, c)₂`.

It states that for any linearly ordered type `V` that is order-isomorphic to the ordinal `ω^β`,
and for any 2-coloring of the edges of the complete graph on `V` (represented by
complementary graphs `G_red` and `G_blue`), one of the following must hold:

* There is a `G_red` clique which is order-isomorphic to `ω^β`.
* There is a `G_blue` clique of cardinality `c`.
-/
def OmegaPowerRamsey (β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  let α_ord := ω ^ β
  -- We require V to have an order (LinearOrder)
  ∀ (V : Type u) [LinearOrder V] [LE (Quotient.out α_ord).α],
  Nonempty (V ≃o α_ord.out.α) →
  ∀ (G_red G_blue : SimpleGraph V), IsCompl G_red G_blue →
    -- ...there is either a red K_α
    (∃ (s : Set V), G_red.IsClique s ∧ Nonempty (s ≃o α_ord.out.α)) ∨
   -- ...or there is a blue K_c.
   -- For the blue clique, size 'c' is enough (if c is finite),
    (∃ (s : Set V), G_blue.IsClique s ∧ #s = c)
