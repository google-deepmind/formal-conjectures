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

Let $f(n)$ be the maximum number of unique subgraphs in a graph on $n$ vertices.
Bradač and Christoph proved that $f(n) = o(2^{\binom{n}{2}} / n!)$.

*Reference:* [erdosproblems.com/426](https://www.erdosproblems.com/426)

[EnEr72] Entringer, R. C. and Erdős, P., _On the number of unique subgraphs of a graph_.
J. Combin. Theory Ser. B 13 (1972), 112-115.

[HaSc73] Harary, F. and Schwenk, A. J., _On the number of unique subgraphs_.
J. Combin. Theory Ser. B 15 (1973), 156-160.

[Br75] Brouwer, A. E., _A note on unique subgraphs_.
J. Combin. Theory Ser. B 18 (1975), 184-185.

[BrCh24] Bradač, D. and Christoph, M., _Unique subgraphs are rare_.
arXiv:2410.16233 (2024).
-/

open SimpleGraph

namespace Erdos426

/--
Two subgraphs of a graph $G$ are isomorphic if there exists a graph isomorphism
between their coerced graphs (viewed as simple graphs on their respective
vertex subtypes).
-/
def SubgraphIsomorphic {V : Type*} {G : SimpleGraph V}
    (H₁ H₂ : G.Subgraph) : Prop :=
  Nonempty (H₁.coe ≃g H₂.coe)

/--
A subgraph $H$ of $G$ is a "unique subgraph" if it is the only subgraph of $G$
in its isomorphism class: every subgraph $H'$ of $G$ isomorphic to $H$ must equal $H$.
-/
def IsUniqueSubgraph {V : Type*} {G : SimpleGraph V}
    (H : G.Subgraph) : Prop :=
  ∀ H' : G.Subgraph, SubgraphIsomorphic H H' → H' = H

/--
The number of unique subgraphs of a graph $G$ on $n$ vertices.
-/
noncomputable def numUniqueSubgraphs {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard {H : G.Subgraph | IsUniqueSubgraph H}

/--
$f(n)$ is the maximum number of unique subgraphs over all graphs on $n$ vertices.
-/
noncomputable def maxUniqueSubgraphs (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n), numUniqueSubgraphs G = k}

/--
Erdős Problem 426 (Disproved):

We say $H$ is a unique subgraph of $G$ if there is exactly one way to find $H$ as a
subgraph (not necessarily induced) of $G$. Let $f(n)$ be the maximum number of
distinct unique subgraphs in a graph on $n$ vertices.

A problem of Erdős and Entringer [EnEr72], who constructed a graph with
$\gg 2^{\binom{n}{2} - O(n^{3/2+o(1)})}$ many unique subgraphs. This was improved by
Harary and Schwenk [HaSc73], and then further by Brouwer [Br75], who constructed a graph
with $\gg 2^{\binom{n}{2} - O(n)} / n!$ many unique subgraphs.

Note that there are approximately $2^{\binom{n}{2}} / n!$ non-isomorphic graphs on $n$
vertices, so the bound in the problem statement is trivially best possible.

Erdős believed Brouwer's construction was essentially best possible, but
Spencer suggested that $\gg 2^{\binom{n}{2}} / n!$ might be achievable. Erdős offered
100 dollars for such a construction and 25 dollars for a disproof.

Bradač and Christoph [BrCh24] proved the answer is no:
$$f(n) = o(2^{\binom{n}{2}} / n!).$$
Quantitatively, the $o(1)$ factor can be taken to be $O(\log \log \log n / \log \log n)$.
-/
@[category research solved, AMS 5]
theorem erdos_426 :
    Filter.Tendsto
      (fun n : ℕ =>
        (maxUniqueSubgraphs n : ℝ) /
        ((2 : ℝ) ^ (n.choose 2) / (Nat.factorial n : ℝ)))
      Filter.atTop
      (nhds 0) := by
  sorry

end Erdos426
