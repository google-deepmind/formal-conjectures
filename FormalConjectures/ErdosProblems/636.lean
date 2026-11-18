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
# Erdős Problem 636

*References:*
- [erdosproblems.com/636](https://www.erdosproblems.com/636)
- [AlKo09] Alon, N. and Kostochka, A. V., *Induced subgraphs with distinct sizes*.
  Random Structures Algorithms 34 (2009), 45-53.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [Er97d] Erdős, Paul, *Some recent problems and results in graph theory*. Discrete Math. (1997),
  81-85.
- [KwSu21] Kwan, M. and Sudakov, B., *Proof of a conjecture on induced subgraphs of Ramsey graphs*.
  Trans. Amer. Math. Soc. 372 (2019), 5571-5594.
  [arXiv:1712.05656](https://arxiv.org/abs/1712.05656)
-/

@[expose] public section

open Filter

namespace Erdos636

/--
`G` contains at least `k` many induced subgraphs which pairwise differ in either the number of
vertices or the number of edges, that is, there is a family of at least `k` many sets of vertices
such that any two of them have different sizes or induce different numbers of edges.
-/
def HasManyDistinctInducedSubgraphs {V : Type*} (G : SimpleGraph V) (k : ℝ) : Prop :=
  ∃ 𝒮 : Set (Set V), 𝒮.Pairwise (fun s t => s.ncard ≠ t.ncard ∨
      (G.induce s).edgeSet.ncard ≠ (G.induce t).edgeSet.ncard) ∧
    k ≤ (𝒮.ncard : ℝ)

set_option linter.style.formal_proof_palomar false in
/--
Suppose $G$ is a graph on $n$ vertices which contains no complete graph or independent set on
$\gg \log n$ many vertices. Must $G$ contain $\gg n^{5/2}$ induced subgraphs which pairwise differ
in either the number of vertices or the number of edges?

A problem of Erdős, Faudree, and Sós (although in [Er93] Erdős credits this question to Alon and
Bollobás). This was proved by Kwan and Sudakov [KwSu21].
-/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos636.lean#L739"]
theorem erdos_636 :
    ∀ C > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.log n → (G.indepNum : ℝ) < C * Real.log n →
        HasManyDistinctInducedSubgraphs G (γ * (n : ℝ) ^ (5 / 2 : ℝ)) := by
  sorry

/--
Erdős, Faudree, and Sós proved that there exist $\gg n^{3/2}$ many such subgraphs, as stated on
erdosproblems.com. Section 2 of [KwSu21] describes two short proofs of this weaker bound.
-/
@[category research solved, AMS 5]
theorem erdos_636.variants.erdos_faudree_sos :
    ∀ C > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.log n → (G.indepNum : ℝ) < C * Real.log n →
        HasManyDistinctInducedSubgraphs G (γ * (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

/--
Erdős, Faudree, and Sós note that the exponent $5/2$ would be best possible: there are graphs on
$n$ vertices with no complete graph or independent set on $\gg \log n$ many vertices which contain
only $O(n^{5/2})$ induced subgraphs that pairwise differ in either the number of vertices or the
number of edges. For example, the random graph $G(n, 1/2)$ has this property with high
probability. This is the remark following Theorem 1.1 in [KwSu21], where it is proved in sketch
form by a concentration inequality and a union bound; see also [AlKo09, Section 4].
-/
@[category research solved, AMS 5]
theorem erdos_636.variants.best_possible :
    ∃ C > (0 : ℝ), ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.log n ∧ (G.indepNum : ℝ) < C * Real.log n ∧
        ¬ HasManyDistinctInducedSubgraphs G (K * (n : ℝ) ^ (5 / 2 : ℝ)) := by
  sorry

end Erdos636
