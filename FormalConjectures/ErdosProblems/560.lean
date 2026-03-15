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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SizeRamsey

/-!
# Erdős Problem 560

*Reference:* [erdosproblems.com/560](https://www.erdosproblems.com/560)

Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such
that there is a graph $H$ with $m$ edges such that in any 2-colouring of the
edges of $H$ there is a monochromatic copy of $G$.

Determine $\hat{R}(K_{n,n})$, where $K_{n,n}$ is the complete bipartite graph with $n$
vertices in each component.

Known bounds:
$$\frac{1}{60} n^2 \cdot 2^n < \hat{R}(K_{n,n}) < \frac{3}{2} n^3 \cdot 2^n$$

The lower bound (for $n \geq 6$) was proved by Erdős and Rousseau [ErRo93].
The upper bound was proved by Erdős, Faudree, Rousseau, and Schelp [EFRS78b]
and Nešetřil and Rödl [NeRo78].

Conlon, Fox, and Wigderson [CFW23] conjecture that $\hat{R}(K_{n,n}) \asymp n^3 \cdot 2^n$.

[ErRo93] Erdős, P. and Rousseau, C.C., *The size Ramsey number of a complete bipartite
graph*, Discrete Mathematics, 1993.

[EFRS78b] Erdős, P., Faudree, R.J., Rousseau, C.C., and Schelp, R.H., *The size Ramsey
number*, Periodica Mathematica Hungarica, 1978.

[NeRo78] Nešetřil, J. and Rödl, V., *The Ramsey property for graphs with forbidden complete
subgraphs*, Journal of Combinatorial Theory, Series B, 1978.

[CFW23] Conlon, D., Fox, J., and Wigderson, Y., *Ramsey numbers of books and
quasirandomness*, Combinatorica, 2023.
-/

open SimpleGraph

namespace Erdos560

/--
Erdős Problem 560, lower bound [ErRo93]:

For all $n \geq 6$, $\hat{R}(K_{n,n}) > \frac{1}{60} n^2 \cdot 2^n$.
-/
@[category research solved, AMS 5]
theorem erdos_560.variants.lower_bound :
    ∀ n : ℕ, n ≥ 6 →
      (sizeRamsey (completeBipartiteGraph (Fin n) (Fin n)) (completeBipartiteGraph (Fin n) (Fin n)) : ℝ) >
        (1 / 60 : ℝ) * (n : ℝ) ^ 2 * 2 ^ n := by
  sorry

/--
Erdős Problem 560, upper bound [EFRS78b, NeRo78]:

For all $n \geq 1$, $\hat{R}(K_{n,n}) < \frac{3}{2} n^3 \cdot 2^n$.
-/
@[category research solved, AMS 5]
theorem erdos_560.variants.upper_bound :
    ∀ n : ℕ, n ≥ 1 →
      (sizeRamsey (completeBipartiteGraph (Fin n) (Fin n)) (completeBipartiteGraph (Fin n) (Fin n)) : ℝ) <
        (3 / 2 : ℝ) * (n : ℝ) ^ 3 * 2 ^ n := by
  sorry

/--
Erdős Problem 560, conjecture [CFW23]:

$\hat{R}(K_{n,n}) \asymp n^3 \cdot 2^n$, i.e., there exist constants $C_1, C_2 > 0$ and $N_0$
such that for all $n \geq N_0$,
$$C_1 \cdot n^3 \cdot 2^n \leq \hat{R}(K_{n,n}) \leq C_2 \cdot n^3 \cdot 2^n.$$
-/
@[category research open, AMS 5]
theorem erdos_560 :
    ∃ C₁ : ℝ, C₁ > 0 ∧ ∃ C₂ : ℝ, C₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C₁ * (n : ℝ) ^ 3 * 2 ^ n ≤
        (sizeRamsey (completeBipartiteGraph (Fin n) (Fin n)) (completeBipartiteGraph (Fin n) (Fin n)) : ℝ) ∧
      (sizeRamsey (completeBipartiteGraph (Fin n) (Fin n)) (completeBipartiteGraph (Fin n) (Fin n)) : ℝ) ≤
        C₂ * (n : ℝ) ^ 3 * 2 ^ n := by
  sorry

end Erdos560
