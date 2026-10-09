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
# Graffiti conjecture 292

*References:*
- S. Fajtlowicz, *Written on the Wall* (July 2004 version), conjecture 292 (p. 80) and the
  definition of the gravity matrix (p. 52).
  [Copy of the source](https://github.com/RoucairolMilo/refutation-COCOON2022/blob/795ff6797ee3875cd36d715515099a48568a451a/wow-july2004.pdf).
- [Refutation of Spectral Graph Theory Conjectures with Search Algorithms](https://arxiv.org/abs/2409.18626)
  by *Milo Roucairol and Tristan Cazenave*. Table 1 lists conjecture 292 as open. Section 5.2
  gives the gravity matrix of *Written on the Wall* and notes that another survey uses a
  different definition.
- [A Proof of Graffiti 292](https://agnt.gg/whitepapers/a-proof-of-graffiti-292.html)
  by *Nathan Wilbanks and Annie*, AGNT Labs (2026).

The source fixes two conventions. Eigenvalues are those of the adjacency matrix (p. 1).
Conjectures that involve distance are only for connected graphs (p. 2).

The gravity matrix is `SimpleGraph.gravity`. The source does not define the mean of a matrix.
`graffiti_292` takes the mean over all $n^2$ entries (`SimpleGraph.meanGravity`).
`graffiti_292.variants.off_diagonal_mean` takes it over the $n(n-1)$ off-diagonal entries
(`SimpleGraph.meanGravityOffDiagonal`).
-/

@[expose] public section

namespace Graffiti292

open SimpleGraph

/-- **Graffiti 292.** Let $G$ be a connected graph on $n$ vertices with girth at least $5$.
Then the least positive adjacency eigenvalue of $G$ is at most $n / \overline{Gr}$, where
$\overline{Gr}$ is the mean of the gravity matrix of $G$.

Here `i` indexes the least positive eigenvalue. Acyclic graphs have `egirth = ⊤`, so they
satisfy the girth hypothesis. -/
@[category research solved, AMS 5 15, formal_proof using lean4 at
  "https://github.com/agnt-gg/graffiti-lean/blob/cceea87d0c42d56701ec3dea4f647b8a4bcf0309/Graffiti/Graffiti292.lean#L20"]
theorem graffiti_292 {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth) (i : α)
    (hpos : 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i)
    (hleast : ∀ j, 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues j →
      (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues j) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ Fintype.card α / G.meanGravity := by
  sorry

/-- **Graffiti 292, off-diagonal mean.** The statement of `graffiti_292`, with the mean of the
gravity matrix taken over the $n(n-1)$ off-diagonal entries. -/
@[category research solved, AMS 5 15, formal_proof using lean4 at
  "https://github.com/agnt-gg/graffiti-lean/blob/cceea87d0c42d56701ec3dea4f647b8a4bcf0309/Graffiti/Graffiti292.lean#L33"]
theorem graffiti_292.variants.off_diagonal_mean {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth)
    (i : α) (hpos : 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i)
    (hleast : ∀ j, 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues j →
      (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues j) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤
      Fintype.card α / G.meanGravityOffDiagonal := by
  sorry

/-- The hypotheses of `graffiti_292` can hold: $K_2$ is connected and acyclic. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 2)).Connected ∧ 5 ≤ (⊤ : SimpleGraph (Fin 2)).egirth := by
  refine ⟨connected_top, ?_⟩
  rw [egirth_eq_top.mpr (IsAcyclic.of_card_le_two (by simp))]
  exact le_top

end Graffiti292
