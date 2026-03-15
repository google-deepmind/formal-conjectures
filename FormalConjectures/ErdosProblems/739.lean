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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős Problem 739

*Reference:* [erdosproblems.com/739](https://www.erdosproblems.com/739)

If a graph has infinite chromatic number $\mathfrak{m}$, must every infinite cardinal
$\mathfrak{n} < \mathfrak{m}$ be realized as the chromatic number of some subgraph?

A question of Galvin [Ga73], who proved the case $\mathfrak{m} = \aleph_0$
(i.e., every graph with chromatic number $\aleph_0$ has subgraphs of every finite
chromatic number; note that under the formalization's restriction to infinite
$\mathfrak{n}$, the case $\mathfrak{m} = \aleph_0$ is vacuously true).
Komjáth [Ko88b] proved it is consistent that the answer is no
(with $\mathfrak{m} = \aleph_2$ and $\mathfrak{n} = \aleph_1$,
under $2^{\aleph_0} = 2^{\aleph_1} = 2^{\aleph_2} = \aleph_3$).
Shelah [Sh90] proved that assuming $V = L$, the answer is yes
with $\mathfrak{m} = \aleph_2$ and $\mathfrak{n} = \aleph_1$.
Whether the answer is affirmative under GCH remains open.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
  Combinatorica **1** (1981), 25–42.

[Ga73] Galvin, F., _Chromatic numbers of subgraphs_. Period. Math. Hungar. (1973), 117–119.

[Ko88b] Komjáth, P., _Consistency results on infinite graphs_. Israel J. Math. (1988), 285–294.

[Sh90] Shelah, S., _Incompactness for chromatic numbers of graphs_. (1990), 361–371.
-/

open SimpleGraph Cardinal

universe u

namespace Erdos739

/--
Erdős Problem 739 [Er81]:

If $G$ is a graph with infinite chromatic number $\mathfrak{m}$, then for every infinite
cardinal $\mathfrak{n} < \mathfrak{m}$, there is a subgraph of $G$ with chromatic
number $\mathfrak{n}$.

A question of Galvin [Ga73]. This is not provable
in ZFC: Komjáth [Ko88b] showed it is consistent that the answer is no.
-/
@[category research open, AMS 3 5]
theorem erdos_739 : answer(sorry) ↔
    ∀ {V : Type u} (G : SimpleGraph V)
    (𝔪 : Cardinal.{u}), ℵ₀ ≤ 𝔪 → G.chromaticCardinal = 𝔪 →
    ∀ (𝔫 : Cardinal.{u}), ℵ₀ ≤ 𝔫 → 𝔫 < 𝔪 →
    ∃ (W : Type u) (H : SimpleGraph W),
      H.chromaticCardinal = 𝔫 ∧
      ∃ f : W → V, Function.Injective f ∧ ∀ a b, H.Adj a b → G.Adj (f a) (f b) := by
  sorry

end Erdos739
