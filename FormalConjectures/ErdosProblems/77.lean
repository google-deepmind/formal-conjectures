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
# Erdős Problem 77

*References:*
- [erdosproblems.com/77](https://www.erdosproblems.com/77)
- [BBCGHMST24] Balister, P. and Bollobás, B. and Campos, M. and Griffiths, S. and Hurley, E. and
  Morris, R. and Sahasrabudhe, J. and Tiba, M., Upper bounds for multicolour Ramsey numbers.
  arXiv:2410.17197 (2024).
- [CGMS23] Campos, Marcelo and Griffiths, Simon and Morris, Robert and Sahasrabudhe, Julian, An
  exponential improvement for diagonal Ramsey. arXiv:2303.09521 (2023).
- [Er88] Erdős, P, Problems and results in combinatorial analysis and graph theory. Discrete Math.
  (1988), 81-92.
- [Er93] Erdős, Paul, Some of my favorite solved and unsolved problems in graph theory. Quaestiones
  Math. (1993), 333-350.
- [GNNW24] Gupta, P. and Ndiaye, N. and Norin, S. and Wei, L., Optimizing the CGMS upper bound on
  Ramsey numbers. arXiv:2407.19026 (2024).
-/

@[expose] public section

open scoped Topology

namespace Erdos77

/--
If $R(k)$ is the Ramsey number for $K_k$, the minimal $n$ such that every $2$-colouring of the edges
of $K_n$ contains a monochromatic copy of $K_k$, then find the value of
$$\lim_{k\to \infty}R(k)^{1/k}.$$

This problem is #3 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_77 :
    Filter.Tendsto (fun k : ℕ ↦ (SimpleGraph.diagonalRamsey k : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (𝓝 answer(sorry)) := by
  sorry

-- TODO: Add variants of the problem.

end Erdos77
