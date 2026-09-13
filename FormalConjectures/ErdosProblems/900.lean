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

import FormalConjecturesUtil

/-!
# Erdős Problem 900

*References:*
- [erdosproblems.com/900](https://www.erdosproblems.com/900)
- [AKS81] Ajtai, Miklós and Komlós, János and Szemerédi, Endre, *The longest path in a random
  graph*. Combinatorica (1981), 1--12.
- [Er78] Erdős, Paul, *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*. (1982),
  59--79.
-/

open Filter

open scoped Topology

namespace Erdos900

/--
The uniform probability that a labelled graph on $n$ vertices with exactly $m$ edges satisfies
`P`. This is the Erdős–Rényi model $G(n,m)$. If no such graph exists, the value is $0$.
-/
noncomputable def gnmProb (n m : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ({G : SimpleGraph (Fin n) | G.edgeSet.ncard = m ∧ P G}.ncard : ℝ) /
    ({G : SimpleGraph (Fin n) | G.edgeSet.ncard = m}.ncard)

/--
There is a function $f:(1/2,\infty)\to \mathbb{R}$ such that $f(c)\to 0$ as $c\to 1/2$ and
$f(c)\to 1$ as $c\to \infty$ and every random graph with $n$ vertices and $cn$ edges has
(with high probability) a path of length at least $f(c)n$.

This was proved by Ajtai, Komlós, and Szemerédi [AKS81].
-/
@[category research solved, AMS 5]
theorem erdos_900 : ∃ f : ℝ → ℝ,
    Tendsto f (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) ∧
    Tendsto f atTop (𝓝 1) ∧
    ∀ c > (1 / 2 : ℝ),
      Tendsto (fun n : ℕ =>
        gnmProb n ⌊c * n⌋₊ fun G =>
          ∃ u v : Fin n, ∃ p : G.Walk u v, p.IsPath ∧ f c * n ≤ p.length)
        atTop (𝓝 1) := by
  sorry

end Erdos900
