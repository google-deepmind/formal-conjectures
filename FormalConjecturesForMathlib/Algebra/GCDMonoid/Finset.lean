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

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Defs

namespace Finset

/-- The least common multiple of ${n+1, \dotsc, n+k}$. -/
def lcmInterval {α : Type*} [AddMonoid α] [CommMonoidWithZero α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id

end Finset
