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

import FormalConjectures.Util.ProblemImports

/-!
# Bounded Burnside problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Burnside_problem#Bounded_Burnside_problem)
-/

/--
Let $G$ be a finitely generated group, and assume there exists $n$ such that for every $g$ in $G$,
$g^n = 1$. Is $G$ necessarily finite?
-/
@[category research open, AMS 20]
theorem bounded_burnside_problem :
    (∀ (G : Type) [Group G] (fin_gen : Group.FG G)
      (n : ℕ) (hn : n > 0) (bounded : ∀ g : G, g^n = 1), Finite G) ↔
    answer(sorry) := by
  sorry
