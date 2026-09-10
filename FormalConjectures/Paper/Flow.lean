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

public import FormalConjecturesUtil

/-!
# Tutte's 5-flow conjecture

## References

* [D. West, *Tutte's 5-flow Conjecture*](https://dwest.web.illinois.edu/openp/tut5flow.html)
* [P. D. Seymour, *Nowhere-zero 6-flows*](https://doi.org/10.1016/0095-8956(81)90058-7)
-/

namespace Graph

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α]

/-- Does every graph without bridges admit an everywhere nonzero `5`-flow? -/
@[category research open, AMS 5]
theorem tutte5Flow : answer(sorry) ↔
    ∀ (α β : Type) [DecidableEq α] (G : Graph α β) [Fintype E(G)], (∀ e : β, ¬ G.IsBridge e) →
      ∃ (O : Orientation G) (f : β → ℤ),
        IsFlow O (G.zeroKNetwork 5) f ∧ ∀ e ∈ G.edgeSet, f e ≠ 0 := by
  sorry

/-- Every graph without bridges admits an everywhere nonzero `6`-flow. -/
@[category research solved, AMS 5]
theorem tutte6Flow
    {α β : Type*} [DecidableEq α] {G : Graph α β} [Fintype E(G)] (hG : ∀ e : β, ¬ G.IsBridge e) :
    ∃ (O : Orientation G) (f : β → ℤ),
      IsFlow O (G.zeroKNetwork 6) f ∧ ∀ e ∈ G.edgeSet, f e ≠ 0 := by
  sorry

end Graph
