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
# Erdős Problem 717

*References:*
- [erdosproblems.com/717](https://www.erdosproblems.com/717)
- [ErFa81] Erdős, Paul and Fajtlowicz, Siemion, *On the conjecture of Hajós*. Combinatorica 1
  (1981), 141-143. [PDF](https://www.renyi.hu/~p_erdos/1981-17.pdf)
- [FLS13] Fox, Jacob and Lee, Choongbum and Sudakov, Benny, *Chromatic number, clique
  subdivisions, and the conjectures of Hajós and Erdős-Fajtlowicz*. Combinatorica 33 (2013),
  181-197. [arXiv:1107.1920](https://arxiv.org/abs/1107.1920)
-/

@[expose] public section

open Filter Topology

namespace Erdos717

/-- The edges of $K_r$ on `Fin r`, each written as a pair `(i, j)` with `i < j`. -/
abbrev CliqueEdge (r : ℕ) := {e : Fin r × Fin r // e.1 < e.2}

/-- The vertices of a walk other than its two endpoints. -/
def walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

/--
A subdivision of the complete graph $K_r$ in `G`: `r` distinct branch vertices, and for each
edge `(i, j)` of $K_r$ a path in `G` from the `i`th to the `j`th branch vertex. The interiors of
these paths are pairwise disjoint and contain no branch vertex.
-/
structure CliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  branch : Fin r ↪ V
  path : ∀ e : CliqueEdge r, G.Walk (branch e.1.1) (branch e.1.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e, Disjoint (walkInteriorSet (path e)) (Set.range branch)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e)) (walkInteriorSet (path f))

/-- `G` contains a subdivision of the complete graph $K_r$. -/
def ContainsCliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (CliqueSubdivision G r)

open scoped Classical in
/--
$\sigma(G)$: the largest `r` such that `G` contains a subdivision of $K_r$.

A subdivision of $K_r$ has `r` distinct branch vertices, so it is enough to search `r ≤ |V|`.
Every graph contains a subdivision of $K_0$, so $\sigma(G) = 0$ only if `V` is empty.
-/
noncomputable def cliqueSubdivisionNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.findGreatest (ContainsCliqueSubdivision G) (Fintype.card V)

/-- The complete graph $K_1$ has no edges. -/
@[category API, AMS 5]
theorem CliqueEdge.isEmpty_one : IsEmpty (CliqueEdge 1) :=
  ⟨fun e => (lt_irrefl e.1.1) (Subsingleton.elim e.1.2 e.1.1 ▸ e.2)⟩

/-- A single vertex is a subdivision of $K_1$. -/
@[category test, AMS 5]
theorem containsCliqueSubdivision_one {V : Type*} (G : SimpleGraph V) (v : V) :
    ContainsCliqueSubdivision G 1 := by
  have := CliqueEdge.isEmpty_one
  exact ⟨{
    branch := ⟨fun _ => v, fun a b _ => Subsingleton.elim a b⟩
    path := fun e => isEmptyElim e
    path_isPath := fun e => isEmptyElim e
    interior_avoids_branch := fun e => isEmptyElim e
    interior_pairwise := fun e => isEmptyElim e }⟩

/-- A subdivision of $K_r$ has `r` distinct branch vertices, so `r ≤ |V|`. -/
@[category API, AMS 5]
theorem card_le_of_containsCliqueSubdivision {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r : ℕ} (h : ContainsCliqueSubdivision G r) : r ≤ Fintype.card V := by
  obtain ⟨S⟩ := h
  simpa using Fintype.card_le_of_injective S.branch S.branch.injective

/-- If `G` contains a subdivision of $K_r$, then $r \leq \sigma(G)$. -/
@[category API, AMS 5]
theorem le_cliqueSubdivisionNumber {V : Type*} [Fintype V] {G : SimpleGraph V} {r : ℕ}
    (h : ContainsCliqueSubdivision G r) : r ≤ cliqueSubdivisionNumber G := by
  classical
  exact Nat.le_findGreatest (card_le_of_containsCliqueSubdivision h) h

/-- Every graph with a vertex has $\sigma(G) \geq 1$. -/
@[category test, AMS 5]
theorem one_le_cliqueSubdivisionNumber {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : 1 ≤ cliqueSubdivisionNumber G :=
  le_cliqueSubdivisionNumber (containsCliqueSubdivision_one G (Classical.choice inferInstance))

/--
Let $G$ be a graph on $n$ vertices with chromatic number $\chi(G)$ and let $\sigma(G)$ be the
maximal $k$ such that $G$ contains a subdivision of $K_k$. Is it true that
$$\chi(G) \ll \frac{n^{1/2}}{\log n}\sigma(G)?$$

The answer is yes, proved by Fox, Lee, and Sudakov [FLS13, Theorem 1.1]. We read $\ll$ as: there
is an absolute constant $C > 0$ with this inequality for all graphs on $n \geq 2$ vertices
(for $n = 1$, $\log n = 0$).
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos717.lean#L573"]
theorem erdos_717 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        2 ≤ Fintype.card V →
        (G.chromaticNumber.toNat : ℝ) ≤
          C * (Real.sqrt (Fintype.card V : ℝ) / Real.log (Fintype.card V : ℝ)) *
            (cliqueSubdivisionNumber G : ℝ) := by
  sorry

/--
Erdős and Fajtlowicz [ErFa81, Theorem 3] showed that for almost all graphs on $n$ vertices
$$\chi(G) \gg \frac{n^{1/2}}{\log n}\sigma(G).$$
As in [ErFa81, p. 141], "almost all" means all but $o(2^{\binom{n}{2}})$ labelled graphs on $n$
vertices.
-/
@[category research solved, AMS 5]
theorem erdos_717.variants.erdos_fajtlowicz :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun n : ℕ =>
        (Nat.card {G : SimpleGraph (Fin n) //
          ¬ (C * (Real.sqrt n / Real.log n) * (cliqueSubdivisionNumber G : ℝ) <
            (G.chromaticNumber.toNat : ℝ))} : ℝ) / 2 ^ n.choose 2) atTop (𝓝 0) := by
  sorry

end Erdos717
