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
# The thin tree conjecture

A spanning tree `T` of a multigraph `G` is `α`-thin if every cut `δ(S)` of `G` contains at most
`α |δ_G(S)|` edges of `T`. Goddyn's thin tree conjecture [Go04, Problem 4] asks whether high edge
connectivity alone forces thin spanning trees: is there `f(k) → 0` such that every
`k`-edge-connected multigraph has an `f(k)`-thin spanning tree? The strong form asks for
`f(k) = C / k`. Thin trees give approximation algorithms for the asymmetric travelling salesman
problem [AGMOS17]; Anari and Oveis Gharan found spanning trees of thinness
`poly(log log n) / k` on `n` vertices [AO15, Corollary 1.8].

*References:*
- [AGMOS17] A. Asadpour, M. X. Goemans, A. Mądry, S. Oveis Gharan and A. Saberi, *An
  `O(log n / log log n)`-approximation algorithm for the asymmetric traveling salesman
  problem*, Oper. Res. 65 (2017), 1043–1061.
- [AO15] N. Anari and S. Oveis Gharan, *Effective-resistance-reducing flows, spectrally thin
  trees, and asymmetric TSP*, FOCS 2015, 20–39. arXiv:1411.4613.
- [Go04] L. A. Goddyn, *Some open problems I like*, online problem list (2004), Problem 4.
- [OAI26] OpenAI, *The strong thin tree conjecture*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-strong-thin-tree-conjecture-September-23-2026/paper.pdf
-/

@[expose] public section

open Filter Topology

namespace ThinTreeConjecture

/-- A finite loopless multigraph with vertices `Fin n` and edges `Fin m`; edge `e` joins
`left e` and `right e`, and parallel edges are distinct. -/
structure MultiGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  loopless : ∀ e, left e ≠ right e

namespace MultiGraph

/-- The edges of `T` with exactly one endpoint in `S`. -/
def cut {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m))
    (S : Finset (Fin n)) : Finset (Fin m) :=
  T.filter fun e => (G.left e ∈ S ∧ G.right e ∉ S) ∨
    (G.right e ∈ S ∧ G.left e ∉ S)

/-- The edge set `T` connects all vertices: it meets every nontrivial cut. -/
def Connected {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → (G.cut T S).Nonempty

/-- `T` is a spanning tree: a minimal connected edge set. -/
def SpanningTree {n m : ℕ} (G : MultiGraph n m) (T : Finset (Fin m)) : Prop :=
  G.Connected T ∧ ∀ e ∈ T, ¬ G.Connected (T.erase e)

/-- `G` is `k`-edge-connected: every nontrivial cut has at least `k` edges. -/
def EdgeConnected {n m : ℕ} (G : MultiGraph n m) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    k ≤ (G.cut Finset.univ S).card

end MultiGraph

/--
**Goddyn's thin tree conjecture.** There is `f : ℕ → ℝ` with `f k → 0` such that every
`k`-edge-connected loopless multigraph on at least two vertices has a spanning tree meeting each
nontrivial cut in at most `f k` times the size of the cut.

This follows from the strong form, which was proved by an internal OpenAI model in September 2026
[OAI26].
-/
@[category research solved, AMS 5 68]
theorem thin_tree_conjecture : ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (n m : ℕ), 2 ≤ n → ∀ G : MultiGraph n m, G.EdgeConnected k →
      ∃ T : Finset (Fin m), G.SpanningTree T ∧
        ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
          ((G.cut T S).card : ℝ) ≤ f k * (G.cut Finset.univ S).card := by
  sorry

/--
**The strong thin tree conjecture.** There is an absolute constant `C > 0` such that every
`k`-edge-connected loopless multigraph on at least two vertices has a spanning tree meeting each
nontrivial cut in at most `C / k` times the size of the cut.

This was proved by an internal OpenAI model in September 2026 [OAI26]. The rate `1 / k` is
optimal: with two vertices and `k` parallel edges, a spanning tree uses one of the `k` edges.
-/
@[category research solved, AMS 5 68]
theorem thin_tree_conjecture.variants.strong : ∃ C : ℝ, 0 < C ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (n m : ℕ), 2 ≤ n → ∀ G : MultiGraph n m, G.EdgeConnected k →
      ∃ T : Finset (Fin m), G.SpanningTree T ∧
        ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
          ((G.cut T S).card : ℝ) ≤ (C / (k : ℝ)) * (G.cut Finset.univ S).card := by
  sorry

/-- The strong form implies Goddyn's conjecture, with `f k = C / k`. -/
@[category test, AMS 5 68]
theorem thin_tree_conjecture_of_strong (h : type_of% thin_tree_conjecture.variants.strong) :
    type_of% thin_tree_conjecture := by
  obtain ⟨C, -, hC⟩ := h
  exact ⟨fun k => C / k, tendsto_const_div_atTop_nhds_zero_nat C, hC⟩

end ThinTreeConjecture
