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
import Mathlib.Combinatorics.SimpleGraph.Circulant
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Erdős Problem 809

*Reference:* [erdosproblems.com/809](https://www.erdosproblems.com/809)

Let $k \geq 3$ and define $F_k(n)$ to be the minimal $r$ such that for any graph $G$
on $n$ vertices with $\lfloor n^2/4 \rfloor + 1$ edges, the edges can be $r$-coloured
so that every subgraph isomorphic to $C_{2k+1}$ is rainbow (no colour repeating on the edges).

Is it true that $F_k(n) \sim n^2/8$?

A problem of Burr, Erdős, Graham, and Sós [Er91], who proved that $F_k(n) \gg n^2$.

See also [Erdős Problem 810](https://www.erdosproblems.com/810).

[Er91] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Matematiche (Catania) **47** (1992), no. 2, 231-240 (1993).
-/

open SimpleGraph

namespace Erdos809

/-- For all graphs on $n$ vertices with $\lfloor n^2/4 \rfloor + 1$ edges, there exists an
$r$-edge-coloring such that every subgraph isomorphic to the cycle $C_{2k+1}$ is rainbow. -/
noncomputable def AllAdmitRainbowOddCycleColoring (k n r : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    G.edgeSet.ncard = n ^ 2 / 4 + 1 →
    ∃ c : Sym2 (Fin n) → Fin r,
      ∀ (f : cycleGraph (2 * k + 1) →g G),
        Function.Injective f →
        IsRainbow f c

/--
**Erdős Problem 809**: $F_k(n) \sim n^2/8$ for all $k \geq 3$.

For every $\varepsilon > 0$, for sufficiently large $n$, $F_k(n)$ lies between
$(1-\varepsilon)n^2/8$ and $(1+\varepsilon)n^2/8$.
-/
@[category research open, AMS 5]
theorem erdos_809 : answer(sorry) ↔
    ∀ (k : ℕ), k ≥ 3 → ∀ (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        (∃ r : ℕ, (↑r : ℝ) ≤ (1 + ε) * ↑n ^ 2 / 8 ∧
          AllAdmitRainbowOddCycleColoring k n r) ∧
        (∀ r : ℕ, (↑r : ℝ) < (1 - ε) * ↑n ^ 2 / 8 →
          ¬AllAdmitRainbowOddCycleColoring k n r) := by
  sorry

end Erdos809
