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
# Erdős Problem 552

*References:*
- [erdosproblems.com/552](https://www.erdosproblems.com/552)
- [BEFRS89] Burr, S. and Erdős, P. and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H., Some
  complete bipartite graph-tree Ramsey numbers. Graph theory in memory of G. A. Dirac (Sandbjerg,
  1985) (1989), 79-89.
- [Ch97] Chen, G., *A result on $C_4$-star Ramsey numbers*. Discrete Mathematics **163** (1997),
  243-246.
-/

@[expose] public section

namespace Erdos552

/--
Determine the Ramsey number
$$R(C_4, S_n),$$
where $S_n=K_{1,n}$ is the star on $n+1$ vertices.

A problem of Burr, Erdős, Faudree, Rousseau, and Schelp [BEFRS89].

This problem is #19 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_552.parts.i :
    ∀ (n : ℕ),
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin n)) =
        answer(sorry) := by
  sorry

/--
In particular, is it true that, for any $c > 0$, there are infinitely many $n$ such that
$$R(C_4, S_n) \leq n + \sqrt{n} - c?$$
-/
@[category research open, AMS 5]
theorem erdos_552.parts.ii : answer(sorry) ↔
    ∀ (c : ℝ), 0 < c →
      Set.Infinite {n : ℕ |
        (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
          (completeBipartiteGraph (Fin 1) (Fin n)) : ℝ) ≤ (n : ℝ) + Real.sqrt n - c} := by
  sorry

/--
Burr, Erdős, Faudree, Rousseau and Schelp also asked whether $f(n + 1) \le f(n) + 2$ for all $n$,
where $f(n) = R(C_4, S_n)$. Chen [Ch97] proved this for $n \ge 1$. It fails for $n = 0$, since
$R(C_4, S_1) = 4$ and $R(C_4, S_0) = 1$.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/agnt-gg/erdos-lean/blob/8e5972f4e6787049b168e5350b1a2badc9eb8bcd/Erdos/Erdos552.lean#L292"]
theorem erdos_552.variants.succ_le_add_two (n : ℕ) (hn : 1 ≤ n) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin (n + 1))) ≤
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin n)) + 2 := by
  sorry

-- TODO: Add variants of the problem.

end Erdos552
