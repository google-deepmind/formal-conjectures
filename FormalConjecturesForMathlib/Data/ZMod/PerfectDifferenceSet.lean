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

import Mathlib.Data.ZMod.Defs

/--
A perfect difference set modulo `n` is a set `D` such that the map `(a, b) ↦ a - b` from
`D.offDiag` to `{x : ZMod n | x ≠ 0}` is a bijection.
-/
def IsPerfectDifferenceSet (D : Set ℕ) (n : ℕ) : Prop :=
  D.offDiag.BijOn (fun (a, b) => (a - b : ZMod n)) {x : ZMod n | x ≠ 0}
