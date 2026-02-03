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

import Mathlib.Order.Interval.Finset.Defs

variable {β : Type*} [Preorder β]
variable {S : Set β} {a b : β}

namespace Set

theorem finite_inter_Iio [LocallyFiniteOrderBot β] :
    (S ∩ Iio b).Finite :=
  Set.finite_Iio b |>.inter_of_right S

noncomputable instance [LocallyFiniteOrderBot β] : Fintype (S ∩ Iio b : Set β) :=
  Set.finite_inter_Iio.fintype

theorem finite_inter_Icc [LocallyFiniteOrder β] [OrderBot β] :
    (S ∩ Icc a b).Finite :=
  Set.finite_Icc a b |>.inter_of_right S

noncomputable instance [LocallyFiniteOrder β] [OrderBot β] : Fintype (S ∩ Icc a b : Set β) :=
  Set.finite_inter_Icc.fintype

end Set
