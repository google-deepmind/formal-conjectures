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
# Erdős Problem 79

*Reference:* [erdosproblems.com/79](https://www.erdosproblems.com/79)

We say $G$ is *Ramsey size linear* if $\hat{r}(G,H) \ll m$ for all graphs $H$ with $m$ edges
and no isolated vertices, where $\hat{r}$ denotes the size Ramsey number.

Are there infinitely many graphs $G$ which are not Ramsey size linear but such
that all of their proper subgraphs are?

[EFRS93] Erdős, P., Faudree, R., Rousseau, C., and Schelp, R., _Ramsey size linear graphs_.
Combin. Probab. Comput. (1993), 389-399.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics, Paul Erdős is Eighty, Vol. 2 (1996), 1–25.

[Wi24] Wigderson, Y., _Infinitely many minimally Ramsey size-linear graphs_.
arXiv:2409.05931 (2024).
-/

open SimpleGraph

namespace Erdos79

/-- **Erdős Problem 79**: Are there infinitely many graphs which are not Ramsey
    size linear but all of whose proper subgraphs are? A graph $H$ is a proper subgraph
    of $G$ if $H$ embeds into $G$ (as a subgraph) but $G$ does not embed into $H$.

    Asked by Erdős, Faudree, Rousseau, and Schelp [EFRS93][Er95].
    Proved by Wigderson [Wi24]. $K_4$ is the only explicitly known example. -/
@[category research solved, AMS 5]
theorem erdos_79 : answer(True) ↔
    ∀ N : ℕ, ∃ (p : ℕ) (G : SimpleGraph (Fin p)),
      p ≥ N ∧
      ¬ IsRamseySizeLinear G ∧
      ∀ (q : ℕ) (H : SimpleGraph (Fin q)),
        H.IsContained G →
        ¬ G.IsContained H →
        IsRamseySizeLinear H := by
  sorry

end Erdos79
