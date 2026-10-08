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

public import Mathlib.Order.Nat

public section

namespace Nat
variable {p : ℕ → Prop} [DecidablePred p] {n : ℕ}

lemma find_of_isLeast (hn : IsLeast {n | p n} n) : Nat.find (p := p) ⟨n, hn.1⟩ = n := by
  rw [find_eq_iff]; exact ⟨hn.1, fun m hmn hm ↦ hmn.not_ge <| hn.2 hm⟩

end Nat
