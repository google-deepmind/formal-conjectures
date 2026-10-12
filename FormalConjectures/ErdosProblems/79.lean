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
# Erdős Problem 79

*References:*
- [erdosproblems.com/79](https://www.erdosproblems.com/79)
- [EFRS93] Erdős, P., Faudree, R. J., Rousseau, C. C. and Schelp, R. H., Ramsey size linear graphs.
  Combin. Probab. Comput. (1993), 389-399.
- [Wi24] Wigderson, Y., Infinitely many minimally non-Ramsey size linear graphs.
  arXiv:2409.05931 (2024).
-/

@[expose] public section

namespace Erdos79

open scoped Classical in
/--
We say $G$ is Ramsey size linear if $R(G,H)\ll m$ for all graphs $H$ with $m$ edges and
no isolated vertices.

Are there infinitely many graphs $G$ which are not Ramsey size linear but such that all of
its proper subgraphs are?

Asked by Erdős, Faudree, Rousseau, and Schelp [EFRS93]. $K_4$ was long the only known example.
Wigderson [Wi24] proved that there are infinitely many such graphs.
-/
@[category research solved, AMS 5]
theorem erdos_79 : answer(True) ↔
    ∀ (N : ℕ), ∃ (n : ℕ) (_ : N ≤ n) (G : SimpleGraph (Fin n)),
      ¬ G.IsRamseySizeLinear ∧
      ∀ H : G.Subgraph, H < ⊤ → H.coe.IsRamseySizeLinear := by
  sorry

-- TODO: Add variants of the problem.

end Erdos79
