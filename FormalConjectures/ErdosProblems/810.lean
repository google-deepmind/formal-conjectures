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

namespace Erdos810

-- English version (Erdős Problem 810):
-- "Does there exist ε > 0 such that, for all sufficiently large n, there exists
--  a graph G on n vertices with at least ε n^2 edges whose edges can be coloured
--  with n colours so that every 4-cycle C4 receives 4 distinct colours?"

def ExistsDenseC4RainbowGraph (_ε : ℝ) (_n : ℕ) : Prop := False


@[category research open, AMS 5]
theorem erdos_810 :
    (∃ ε : ℝ, ε > 0 ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ExistsDenseC4RainbowGraph ε n) ↔
      answer(sorry) := by
  sorry

end Erdos810
