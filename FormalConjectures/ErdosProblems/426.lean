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
# Erdős Problem 426

*References:*
- [erdosproblems.com/426](https://www.erdosproblems.com/426)
- [Er76b] Erdős, P., *Problems and results in graph theory and combinatorial analysis*.
  Proceedings of the Fifth British Combinatorial Conference (1976), 169-192.
- [EnEr72] Entringer, R. C. and Erdős, Paul, *On the number of unique subgraphs of a graph*.
  J. Combinatorial Theory Ser. B (1972), 112-115.
- [HaSc73] Harary, Frank and Schwenk, Allen J., *On the number of unique subgraphs*.
  J. Combinatorial Theory Ser. B (1973), 156-160.
- [Br75] Brouwer, A. E., *Note: "On the number of unique subgraphs of a graph"
  (J. Combinatorial Theory Ser. B 13 (1972), 112-115) by R. C. Entringer and P. Erdős*.
  J. Combinatorial Theory Ser. B (1975), 184-185.
- [BrCh24] Bradač, D. and Christoph, M., *Unique subgraphs are rare*. arXiv:2410.16233 (2024).
-/

open Filter SimpleGraph

namespace Erdos426

/-- Sanity check: the empty graph `⊥` is a unique subgraph of itself. Its only subgraph is `⊥`
(everything `≤ ⊥` equals `⊥`), which is isomorphic to `⊥` via the identity. -/
@[category test, AMS 5]
theorem isUniqueSubgraph_bot_bot {V : Type*} : IsUniqueSubgraph (⊥ : SimpleGraph V) ⊥ := by
  refine ⟨⊥, ⟨le_refl _, ⟨Iso.refl⟩⟩, ?_⟩
  rintro G' ⟨hle, -⟩
  exact le_bot_iff.mp hle

/--
We say $H$ is a unique subgraph of $G$ if there is exactly one way to find $H$ as a subgraph
(not necessarily induced) of $G$. Is there a graph on $n$ vertices with
\[\gg \frac{2^{\binom{n}{2}}}{n!}\]
many distinct unique subgraphs?

Bradač and Christoph [BrCh24] have proved the answer is no: if $f(n)$ is the maximum number of
unique subgraphs in a graph on $n$ vertices then
\[f(n) = o\left(\frac{2^{\binom{n}{2}}}{n!}\right).\]

The $\gg$ below is read as: some constant $c>0$ works for arbitrarily large $n$. The negation
of the proposition on the right is then exactly $f(n) = o(2^{\binom{n}{2}}/n!)$, the form in
which Bradač and Christoph [BrCh24] resolved the problem.
-/
@[category research solved, AMS 5]
theorem erdos_426 : answer(False) ↔
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ (n : ℕ) in atTop, ∃ H : SimpleGraph (Fin n),
      c * ((2 : ℝ) ^ n.choose 2 / n.factorial) ≤ (uniqueSubgraphCount H : ℝ) := by
  sorry

end Erdos426
