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

The source does not define the mean of a matrix. `graffiti_292` takes the mean over all $n^2$
entries. `graffiti_292.variants.off_diagonal_mean` takes it over the $n(n-1)$ off-diagonal
entries.
-/

@[expose] public section

namespace Graffiti292

open SimpleGraph

/-- The gravity matrix of `G`. The $(u, v)$ entry is $0$ if $u = v$, and otherwise
$\frac{d(u) d(v)}{(n - 1) \operatorname{dist}(u, v)}$, where $n$ is the number of vertices.
If no path joins $u$ and $v$, then `G.dist u v = 0` and the entry is $0$, as in the source. -/
noncomputable def gravity {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (u v : α) : ℝ :=
  if u = v then 0
  else (G.degree u * G.degree v : ℝ) / ((Fintype.card α - 1 : ℝ) * G.dist u v)

/-- The mean of the $n^2$ entries of the gravity matrix of `G`. -/
noncomputable def meanGravity {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] : ℝ :=
  (∑ u, ∑ v, gravity G u v) / (Fintype.card α : ℝ) ^ 2

/-- The mean of the $n(n-1)$ off-diagonal entries of the gravity matrix of `G`. -/
noncomputable def meanGravityOffDiagonal {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  (∑ u, ∑ v, gravity G u v) / (Fintype.card α * (Fintype.card α - 1) : ℝ)

/-- **Graffiti 292.** Let $G$ be a connected graph on $n$ vertices with girth at least $5$.
Then the least positive adjacency eigenvalue of $G$ is at most $n / \overline{Gr}$, where
$\overline{Gr}$ is the mean of the gravity matrix of $G$.

Here `i` indexes the least positive eigenvalue. Acyclic graphs have `egirth = ⊤`, so they
satisfy the girth hypothesis. -/
@[category research solved, AMS 5 15, formal_proof using lean4 at
  "https://github.com/agnt-gg/graffiti-292-lean/blob/5e6337907f2f41790f540d28cbfe419e19e44261/Graffiti292.lean#L321"]
theorem graffiti_292 {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth) (i : α)
    (hpos : 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i)
    (hleast : ∀ j, 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues j →
      (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues j) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ Fintype.card α / meanGravity G := by
  sorry

/-- **Graffiti 292, off-diagonal mean.** The statement of `graffiti_292`, with the mean of the
gravity matrix taken over the $n(n-1)$ off-diagonal entries. -/
@[category research solved, AMS 5 15, formal_proof using lean4 at
  "https://github.com/agnt-gg/graffiti-292-lean/blob/5e6337907f2f41790f540d28cbfe419e19e44261/Graffiti292.lean#L334"]
theorem graffiti_292.variants.off_diagonal_mean {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth)
    (i : α) (hpos : 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i)
    (hleast : ∀ j, 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues j →
      (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues j) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤
      Fintype.card α / meanGravityOffDiagonal G := by
  sorry

/-- For $K_2$, each off-diagonal entry of the gravity matrix is $1$, so the mean of the four
entries is $1/2$. This checks the $(n - 1)$ factor and the $n^2$ normalisation. -/
@[category test, AMS 5]
example : meanGravity (⊤ : SimpleGraph (Fin 2)) = 1 / 2 := by
  have h01 : (⊤ : SimpleGraph (Fin 2)).dist 0 1 = 1 := dist_eq_one_iff_adj.mpr (by decide)
  have h10 : (⊤ : SimpleGraph (Fin 2)).dist 1 0 = 1 := dist_eq_one_iff_adj.mpr (by decide)
  simp [meanGravity, gravity, Fin.sum_univ_two, h01, h10, complete_graph_degree]
  norm_num

/-- The hypotheses of `graffiti_292` can hold: $K_2$ is connected and acyclic. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 2)).Connected ∧ 5 ≤ (⊤ : SimpleGraph (Fin 2)).egirth := by
  refine ⟨connected_top, ?_⟩
  rw [egirth_eq_top.mpr (IsAcyclic.of_card_le_two (by simp))]
  exact le_top

end Graffiti292
