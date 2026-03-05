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
# Erdős Problem 738

*Reference:* [erdosproblems.com/738](https://www.erdosproblems.com/738)

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
Combinatorica 1 (1981), 25-42.
-/

open SimpleGraph

namespace Erdos738

/-- A graph has infinite chromatic number: it cannot be properly colored
with finitely many colors. -/
def HasInfiniteChromaticNumber {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, IsEmpty (G.Coloring (Fin n))

/--
Erdős Problem 738 (Gyárfás conjecture) [Er81]:

If $G$ is a graph with infinite chromatic number and $G$ is triangle-free
(contains no $K_3$), must $G$ contain every finite tree as an induced subgraph?
-/
@[category research open, AMS 5]
theorem erdos_738 : answer(sorry) ↔
    ∀ (V : Type*) (G : SimpleGraph V),
    HasInfiniteChromaticNumber G → G.CliqueFree 3 →
    ∀ (m : ℕ) (T : SimpleGraph (Fin m)), T.IsTree →
      Nonempty (T ↪g G) := by
  sorry

end Erdos738
