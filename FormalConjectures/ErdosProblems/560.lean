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
# Erdős Problem 560

*References:*
- [erdosproblems.com/560](https://www.erdosproblems.com/560)
- [EFRS82] Erdős, P. and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H., Ramsey numbers
  for brooms. Proceedings of the thirteenth Southeastern conference on combinatorics, graph
  theory and computing (1982), 283-293.
- [ErRo93] Erdős, P. and Rousseau, C. C., The size Ramsey number of a complete bipartite graph.
  Discrete Math. (1993), 259-262.
- [EFRS78b] Erdős, P. and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H., The size Ramsey
  number. Period. Math. Hungar. (1978), 145-161.
- [NeRo78] Nešetřil, J. and Rödl, V., The structure of critical Ramsey graphs.
  Acta Math. Acad. Sci. Hungar. (1978), 295-300.
- [CFW23] Conlon, D. and Fox, J. and Wigderson, Y., Three early problems on size Ramsey numbers.
  Combinatorica (2023), 743-768.
-/

@[expose] public section

namespace Erdos560

open Filter SimpleGraph
open scoped Asymptotics

local notation "r̂(" n ")" =>
  sizeRamsey (completeBipartiteGraph (Fin n) (Fin n))
    (completeBipartiteGraph (Fin n) (Fin n))

/--
Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such that there
is a graph $H$ with $m$ edges such that in any $2$-colouring of the edges of $H$ there is a
monochromatic copy of $G$.

Determine
$$\hat{R}(K_{n,n}),$$
where $K_{n,n}$ is the complete bipartite graph with $n$ vertices in each component.
-/
@[category research open, question value, AMS 5]
theorem erdos_560 : answer(sorry) = (fun n : ℕ ↦ r̂(n)) := by
  sorry

/--
The lower bound (which holds for $n\geq 6$) was proved by Erdős and Rousseau [ErRo93]:
$$\frac{1}{60}n^22^n<\hat{R}(K_{n,n}).$$
-/
@[category research solved, AMS 5]
theorem erdos_560.variants.lower_bound :
    ∀ (n : ℕ), 6 ≤ n → (1 / 60 : ℝ) * (n : ℝ) ^ 2 * 2 ^ n < r̂(n) := by
  sorry

/--
The upper bound was proved by Erdős, Faudree, Rousseau, and Schelp [EFRS78b] and Nešetřil
and Rödl [NeRo78]:
$$\hat{R}(K_{n,n})<\frac{3}{2}n^32^n.$$
We require $n\geq 1$ because the strict inequality fails for the empty graph.
-/
@[category research solved, AMS 5]
theorem erdos_560.variants.upper_bound :
    ∀ (n : ℕ), 1 ≤ n → (r̂(n) : ℝ) < (3 / 2 : ℝ) * (n : ℝ) ^ 3 * 2 ^ n := by
  sorry

/--
Conlon, Fox, and Wigderson [CFW23] conjecture that
$$\hat{R}(K_{s,t})\asymp s^2t2^s$$
for all $s\leq t$, and so in particular we should have
$$\hat{R}(K_{n,n})\asymp n^32^n.$$
-/
@[category research open, AMS 5]
theorem erdos_560.variants.conlon_fox_wigderson :
    (fun n : ℕ ↦ (r̂(n) : ℝ)) =Θ[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 3 * 2 ^ n) := by
  sorry

end Erdos560
