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
# Erdős Problem 564

*Reference:* [erdosproblems.com/564](https://www.erdosproblems.com/564)
-/

namespace Erdos564

open Combinatorics Real Filter

/--
Let $R_3(n)$ be the minimal $m$ such that if the edges of the $3$-uniform hypergraph on $m$
vertices are $2$-coloured then there is a monochromatic copy of the complete $3$-uniform
hypergraph on $n$ vertices.

Is there some constant $c>0$ such that
$$ R_3(n) \geq 2^{2^{cn}}? $$
-/
@[category research open, AMS 05]
theorem erdos_564 : answer(sorry) ↔
    ∃ c > 0, ∀ᶠ n in atTop, (2 : ℝ)^(2 : ℝ)^(c * n) ≤ hypergraphRamsey 3 n := by
  sorry

end Erdos564
