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
# Graffiti conjecture 295

*References:*
- S. Fajtlowicz, *Written on the Wall* (July 2004 version), conjecture 295 (p. 80) and the
  definition of the gravity matrix (p. 52).
  [Copy of the source](https://github.com/RoucairolMilo/refutation-COCOON2022/blob/795ff6797ee3875cd36d715515099a48568a451a/wow-july2004.pdf).
- [Refutation of Spectral Graph Theory Conjectures with Search Algorithms](https://arxiv.org/abs/2409.18626)
  by *Milo Roucairol and Tristan Cazenave*. Table 1 lists conjecture 295 as open. Section 5.2
  gives the gravity matrix of *Written on the Wall* used here.
- [A Proof of Graffiti 295](https://agnt.gg/whitepapers/a-proof-of-graffiti-295.html)
  by *Nathan Wilbanks and Annie*, AGNT Labs (2026).

Conjectures that involve distance are only for connected graphs (*Written on the Wall*, p. 2).

The distance matrix is `SimpleGraph.distanceMatrix` and the gravity matrix is
`SimpleGraph.gravity`. As in `SimpleGraph.cvetkovic`, eigenvalues are counted with multiplicity
as roots of the characteristic polynomial. The source does not define the mean of a matrix.
`graffiti_295` takes the mean over all $n^2$ entries (`SimpleGraph.meanGravity`).
`graffiti_295.variants.off_diagonal_mean` takes it over the $n(n-1)$ off-diagonal entries
(`SimpleGraph.meanGravityOffDiagonal`).
-/

@[expose] public section

namespace Graffiti295

open SimpleGraph

/-- **Graffiti 295.** Let $G$ be a connected graph on $n$ vertices with girth at least $5$.
Then the number of positive eigenvalues of the distance matrix of $G$, counted with
multiplicity, is at most $n / \overline{Gr}$, where $\overline{Gr}$ is the mean of the gravity
matrix of $G$. Acyclic graphs have `egirth = ⊤`, so they satisfy the girth hypothesis. -/
@[category research solved, AMS 5 15, formal_proof using lean4 at
  "https://github.com/agnt-gg/graffiti-lean/blob/daf0f85c89c6a7914f7ffd99247a2a1549e26389/Graffiti/Graffiti295.lean#L85"]
theorem graffiti_295 {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth) :
    (G.distanceMatrix.charpoly.roots.countP (fun x => 0 < x) : ℝ) ≤
      Fintype.card α / G.meanGravity := by
  sorry

/-- **Graffiti 295, off-diagonal mean.** The statement of `graffiti_295`, with the mean of the
gravity matrix taken over the $n(n-1)$ off-diagonal entries. -/
@[category research solved, AMS 5 15, formal_proof using lean4 at
  "https://github.com/agnt-gg/graffiti-lean/blob/daf0f85c89c6a7914f7ffd99247a2a1549e26389/Graffiti/Graffiti295.lean#L95"]
theorem graffiti_295.variants.off_diagonal_mean {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth) :
    (G.distanceMatrix.charpoly.roots.countP (fun x => 0 < x) : ℝ) ≤
      Fintype.card α / G.meanGravityOffDiagonal := by
  sorry

/-- The hypotheses of `graffiti_295` can hold: $K_2$ is connected and acyclic. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 2)).Connected ∧ 5 ≤ (⊤ : SimpleGraph (Fin 2)).egirth := by
  refine ⟨connected_top, ?_⟩
  rw [egirth_eq_top.mpr (IsAcyclic.of_card_le_two (by simp))]
  exact le_top

end Graffiti295
