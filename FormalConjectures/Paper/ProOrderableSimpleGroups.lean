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
# Simple pro-orderable groups (Kourovka Notebook 1.35(c))

*Reference:* Kourovka Notebook Problem 1.35(c) (Mal'cev–Fuchs), asking whether a
simple pro-orderable group exists.
-/

namespace ProOrderableGroups

variable {G : Type*}

/--
A relation on a group is bi-invariant if it is preserved by both left and right
multiplication.
-/
def IsBiInvariant (G : Type*) [Group G] (r : G → G → Prop) : Prop :=
  (∀ g a b, r a b → r (g * a) (g * b)) ∧
  (∀ g a b, r a b → r (a * g) (b * g))

/--
`ProOrderable G` means every bi-invariant partial order extends to a bi-
 invariant linear order.
-/
def ProOrderable (G : Type*) [Group G] : Prop :=
  ∀ r : G → G → Prop,
    IsPartialOrder G r →
    IsBiInvariant (G := G) r →
    ∃ s : G → G → Prop,
      IsLinearOrder G s ∧ IsBiInvariant (G := G) s ∧ ∀ x y, r x y → s x y

/--
Kourovka Notebook Problem 1.35(c): does there exist a simple pro-orderable group?
-/
@[category research open, AMS 16]
theorem simple_proOrderable_group :
    ∃ (G : Type*) (_ : Group G), IsSimpleGroup G ∧ ProOrderable G := by
  sorry

end ProOrderableGroups
