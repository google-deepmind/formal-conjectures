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
# Erdős Problem 595

*Reference:* [erdosproblems.com/595](https://www.erdosproblems.com/595)

A problem of Erdős and Hajnal. Folkman [Fo70] and Nešetřil and Rödl [NeRo75]
have proved that for every $n \geq 1$ there is a graph $G$ which contains no
$K_4$ and is not the union of $n$ triangle-free graphs.

[Er87] Erdős, P., _Some problems and results on combinatorial number theory_,
Graph theory and its applications: East and West (1987).

[Fo70] Folkman, J., _Graphs with monochromatic complete subgraphs in every edge
coloring_, SIAM J. Appl. Math. 18 (1970), 19-24.

[NeRo75] Nešetřil, J. and Rödl, V., _The Ramsey property for graphs with
forbidden complete subgraphs_, J. Combinatorial Theory Ser. B 20 (1976), 243-249.
-/

namespace Erdos595

/--
Erdős Problem 595 [Er87]:

Is there an infinite graph $G$ which contains no $K_4$ and is not the union
of countably many triangle-free graphs?
-/
@[category research open, AMS 5]
theorem erdos_595 : answer(sorry) ↔
    ∃ (V : Type) (_ : Infinite V) (G : SimpleGraph V),
      G.CliqueFree 4 ∧
        ¬∃ (H : ℕ → SimpleGraph V),
          (∀ i, H i ≤ G) ∧
          (∀ i, (H i).CliqueFree 3) ∧
          (∀ u v, G.Adj u v → ∃ i, (H i).Adj u v) := by
  sorry

end Erdos595
