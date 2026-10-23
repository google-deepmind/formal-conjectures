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
# Graffiti conjecture 290

*References:*
- S. Fajtlowicz, *Written on the Wall* (July 2004 version), conjecture 290 (p. 79) and the
  definition of the gravity matrix (p. 52).
  [Copy of the source](https://github.com/RoucairolMilo/refutation-COCOON2022/blob/795ff6797ee3875cd36d715515099a48568a451a/wow-july2004.pdf).
- [Refutation of Spectral Graph Theory Conjectures with Search Algorithms](https://arxiv.org/abs/2409.18626)
  by *Milo Roucairol and Tristan Cazenave*. Table 1 lists conjecture 290 as open. Section 5.2
  notes that conjecture 290 is easy under the gravity matrix of another survey, and gives the
  gravity matrix of *Written on the Wall* used here.
- [A Proof of Graffiti 290](https://agnt.gg/whitepapers/a-proof-of-graffiti-290.html)
  by *Nathan Wilbanks and Annie*, AGNT Labs (2026).

The source fixes two conventions. Eigenvalues are those of the adjacency matrix (p. 1).
Conjectures that involve distance are only for connected graphs (p. 2).

The "size" of a graph is its number of edges. The gravity matrix is `SimpleGraph.gravity`.
The source does not define the mean of a matrix. `graffiti_290` takes the mean over all $n^2$
entries (`SimpleGraph.meanGravity`). `graffiti_290.variants.off_diagonal_mean` takes it over
the $n(n-1)$ off-diagonal entries (`SimpleGraph.meanGravityOffDiagonal`).
-/

@[expose] public section

namespace Graffiti290

open SimpleGraph

/-- **Graffiti 290.** Let $G$ be a connected graph with $n \ge 2$ vertices, $m$ edges and girth
at least $5$. Let $\lambda_1 \ge \dots \ge \lambda_n$ be its adjacency eigenvalues. Then
$-\lambda_{n-1} \le m / \overline{Gr}$, where $\overline{Gr}$ is the mean of the gravity matrix
of $G$.

`eigenvalues₀` lists the eigenvalues in decreasing order from index $0$, so the second-smallest
eigenvalue $\lambda_{n-1}$ has index $n - 2$. The hypothesis $n \ge 2$ makes it exist. -/
@[category research solved, AMS 5 15, formal_proof using lean4 at
  "https://github.com/agnt-gg/graffiti-lean/blob/cceea87d0c42d56701ec3dea4f647b8a4bcf0309/Graffiti/Graffiti290.lean#L23"]
theorem graffiti_290 {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth)
    (hn : 2 ≤ Fintype.card α) :
    -(G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨Fintype.card α - 2, by omega⟩ ≤
      G.edgeFinset.card / G.meanGravity := by
  sorry

/-- **Graffiti 290, off-diagonal mean.** The statement of `graffiti_290`, with the mean of the
gravity matrix taken over the $n(n-1)$ off-diagonal entries. -/
@[category research solved, AMS 5 15, formal_proof using lean4 at
  "https://github.com/agnt-gg/graffiti-lean/blob/cceea87d0c42d56701ec3dea4f647b8a4bcf0309/Graffiti/Graffiti290.lean#L38"]
theorem graffiti_290.variants.off_diagonal_mean {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth)
    (hn : 2 ≤ Fintype.card α) :
    -(G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨Fintype.card α - 2, by omega⟩ ≤
      G.edgeFinset.card / G.meanGravityOffDiagonal := by
  sorry

/-- The hypotheses of `graffiti_290` can hold: $K_2$ is connected, acyclic and has two
vertices. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 2)).Connected ∧ 5 ≤ (⊤ : SimpleGraph (Fin 2)).egirth ∧
    2 ≤ Fintype.card (Fin 2) := by
  refine ⟨connected_top, ?_, by simp⟩
  rw [egirth_eq_top.mpr (IsAcyclic.of_card_le_two (by simp))]
  exact le_top

end Graffiti290
