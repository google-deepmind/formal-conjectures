/-
Copyright 2025 The Formal Conjectures Authors.

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
Title: Degree sequences in triangle-free graphs
Authors: P. Erdős, S. Fajtlowicz and W. Staton,
Published in Discrete Mathematics 92 (1991) 85–88.
-/

open BigOperators
open Classical

/-- A sequence of natural numbers is **compact** if consecutive terms at distance
`2` differ by `1`. -/
def IsCompactSequence (d : ℕ → ℕ) : Prop :=
  ∀ k, d (k + 2) = d k + 1

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of vertices of `G` having degree `d`. -/
noncomputable def degreeFreq (G : SimpleGraph α) (d : ℕ) : ℕ :=
  (Finset.univ.filter fun v : α => G.degree v = d).card

/-- `δ G` is the minimum degree of `G`. -/
noncomputable def δ (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sInf (Set.range fun v : α => G.degree v)

end SimpleGraph

section lemmas

variable (d : ℕ → ℕ) (n k r : ℕ)

/-- **Lemma 1 (a)** -/
@[category research solved, AMS 5]
lemma lemma1_a
    (h_no_three : ∀ k, d (k + 2) ≠ d k) :
    1 ≤ d (k + 2) - d k := by
  sorry

/-- **Lemma 1 (b)** -/
@[category research solved, AMS 5]
lemma lemma1_b
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    r ≤ d (k + 2 * r) - d k := by
  sorry

/-- **Lemma 2 (a)** -/
@[category research solved, AMS 5]
lemma lemma2_a
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    2 * n * n ≤
      (∑ i ∈ Finset.Icc (2 * n + 1) (4 * n), d i) -
        (∑ i ∈ Finset.Icc 1 (2 * n), d i) := by
  sorry

/-- **Lemma 2 (b)** -/
@[category research solved, AMS 5]
lemma lemma2_b
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    2 * n * n + 2 * n + 1 ≤
      (∑ i ∈ Finset.Icc (2 * n + 1) (4 * n + 1), d i) -
        (∑ i ∈ Finset.Icc 1 (2 * n), d i) := by
  sorry

/-- **Lemma 2 (c)** -/
@[category research solved, AMS 5]
lemma lemma2_c
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    2 * n * n + 2 * n ≤
      (∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 2), d i) -
        (∑ i ∈ Finset.Icc 1 (2 * n + 1), d i) := by
  sorry

/-- **Lemma 2 (d)** -/
@[category research solved, AMS 5]
lemma lemma2_d
    (h_no_three : ∀ i, d (i + 2) ≠ d i) :
    2 * n * n + 4 * n + 2 ≤
      (∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 3), d i) -
        (∑ i ∈ Finset.Icc 1 (2 * n + 1), d i) := by
  sorry

end lemmas

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The degree sequence of a graph, sorted in nondecreasing order. -/
noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

/-- The degree sequence of `G` is **compact** if it satisfies
`IsCompactSequence`. -/
def degreeSequenceCompact (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  IsCompactSequence fun k => (degreeSequence G).getD k 0

/-- **Theorem 1.** If a triangle-free graph has `f = 2`,
then it is bipartite, has minimum degree `1`, and
its degree sequence is compact. -/
@[category research solved, AMS 5]
theorem theorem1 (G : SimpleGraph α) [DecidableRel G.Adj] (h₁ : G.CliqueFree 3) (h₂ : f G = 2) :
    G.IsBipartite ∧ δ G = 1 ∧ degreeSequenceCompact G := by
  sorry

/-- **Lemma 3.** For every `n` there exists a bipartite graph with
`8 n` vertices, minimum degree `n + 1`, and `f = 3`. -/
@[category research solved, AMS 5]
lemma lemma3 (n : ℕ) (hn : 0 < n) :
    ∃ (G : SimpleGraph (Fin (8 * n))) (_ : DecidableRel G.Adj),
      G.IsBipartite ∧ δ G = n + 1 ∧ f G = 3 := by
  sorry

/-- **Lemma 4.** A triangle-free graph can be extended by one to a
triangle-free graph whose new part has minimum degree at least
`2 n` and `f = 3`. -/
@[category research solved, AMS 5]
lemma lemma4 (G : SimpleGraph α) [DecidableRel G.Adj] (h₁ : G.CliqueFree 3) (v : α) :
    ∃ (β : Type*) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : α ↪ β),
      (∀ u w, G.Adj u w ↔ H.Adj (i u) (i w)) ∧
      H.degree (i v) = G.degree v + 1 ∧
      (∀ w ≠ v, H.degree (i w) = G.degree w) ∧
      let J := H.induce (Set.compl (Set.range i))
      J.CliqueFree 3 ∧ f J = 3 ∧ δ J ≥ 2 * Fintype.card α := by
  sorry

/-- **Theorem 2.** Every triangle-free graph is an induced subgraph of one
with `f = 3`. -/
@[category research solved, AMS 5]
theorem theorem2 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    ∃ (β : Type*) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : α ↪ β),
      (∀ u w, G.Adj u w ↔ H.Adj (i u) (i w)) ∧ H.CliqueFree 3 ∧ f H = 3 := by
  sorry

/-- `F n` is the smallest number of vertices of a triangle-free graph
with chromatic number `n` and `f = 3`. -/
@[category research solved, AMS 5]
noncomputable def F (n : ℕ) : ℕ :=
  sInf { p | ∃ (G : SimpleGraph (Fin p)) (_ : DecidableRel G.Adj),
    G.CliqueFree 3 ∧ G.chromaticNumber = n ∧ f G = 3 }

@[category research solved, AMS 5]
theorem F_three : F 3 = 7 := by
  sorry

@[category research solved, AMS 5]
theorem F_four_le : F 4 ≤ 19 := by
  sorry

end SimpleGraph
