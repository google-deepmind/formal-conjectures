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
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Erdős Problem 549

*Reference:* [erdosproblems.com/549](https://www.erdosproblems.com/549)

If $T$ is a tree which is a bipartite graph with $k$ vertices in one class and $2k$
vertices in the other class then $R(T) = 4k - 1$.

This is a special case of a conjecture of Burr [Bu74] (see [547]).

This conjecture is false: Norin, Sun, and Zhao [NSZ16] proved that if $T$ is the
union of two stars on $k$ and $2k$ vertices with an edge joining their centres,
then $R(T) \geq (4.2 - o(1))k$.

[Bu74] Burr, S.A., *Generalized Ramsey theory for graphs — a survey*, 1974, 52-75.

[BuEr76] Burr, S.A. and Erdős, P., *Extremal Ramsey theory for graphs*. Utilitas
Mathematica (1976), 247-258.

[EFRS82] Erdős, P., Faudree, R.J., Rousseau, C.C., and Schelp, R.H., *Ramsey numbers
for brooms*. Proceedings of the Thirteenth Southeastern Conference on Combinatorics,
Graph Theory and Computing (1982), 283-293.

[NSZ16] Norin, S., Sun, Y.R., and Zhao, Y., *Asymptotics of Ramsey numbers of double
stars*. arXiv:1605.03612 (2016).

[DuSt24] Dubó, F.F. and Stein, M., *On the Ramsey number of the double star*.
arXiv:2401.01274 (2024).

[MPY25] Montgomery, R., Pavez-Signé, M., and Yan, J., *Ramsey numbers of trees*.
arXiv:2509.07934 (2025).
-/

open SimpleGraph Finset

namespace Erdos549

/-- The diagonal Ramsey number $R(G)$ for a graph $G$: the minimum
$N$ such that every graph $H$ on $N$ vertices contains a copy of $G$ or its complement
contains a copy of $G$. -/
noncomputable def ramseyNumber {U : Type*} (G : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    G.IsContained H ∨ G.IsContained Hᶜ}

/--
Erdős Problem 549 [EFRS82]:

If $T$ is a tree which is a bipartite graph with $k$ vertices in one class and $2k$
vertices in the other class then $R(T) = 4k - 1$.

The bipartition condition is expressed via a proper 2-coloring where one color
class has $k$ vertices and the other has $2k$ vertices.

This conjecture has been disproved by Norin, Sun, and Zhao [NSZ16].
-/
@[category research solved, AMS 5]
theorem erdos_549 : answer(False) ↔
    ∀ (k : ℕ), k ≥ 1 →
    ∀ (T : SimpleGraph (Fin (3 * k))),
    T.IsTree →
    (∃ c : T.Coloring (Fin 2),
      (Finset.univ.filter (fun v => c v = 0)).card = k ∧
      (Finset.univ.filter (fun v => c v = 1)).card = 2 * k) →
    ramseyNumber T = 4 * k - 1 := by
  sorry

end Erdos549
