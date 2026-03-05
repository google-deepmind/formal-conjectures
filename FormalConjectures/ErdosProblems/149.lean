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
# Erdős Problem 149

The Erdős–Nešetřil conjecture states that the strong chromatic index of any graph with
maximum degree Δ is at most 5Δ²/4.

*Reference:* [erdosproblems.com/149](https://www.erdosproblems.com/149)

[ErNe85] Erdős, P. and Nešetřil, J., proposed at a seminar in Prague (1985).
-/

open SimpleGraph

namespace Erdos149

/-- A set $S$ of edges of $G$ is strongly independent if for any two distinct edges
$e_1, e_2 \in S$, every endpoint $u$ of $e_1$ and every endpoint $v$ of $e_2$ satisfy
$u \neq v$ and $\neg G.\text{Adj}\; u\; v$. Equivalently, $S$ is an independent set in $L(G)^2$
(the square of the line graph of $G$). -/
def IsStronglyIndepEdgeSet {V : Type*} (G : SimpleGraph V)
    (S : Set (Sym2 V)) : Prop :=
  S ⊆ G.edgeSet ∧
  ∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ →
    ∀ u ∈ e₁, ∀ v ∈ e₂, u ≠ v ∧ ¬G.Adj u v

/-- The strong chromatic index $\chi'_s(G)$: the minimum number of strongly
independent edge sets needed to partition the edges of $G$. Equivalently,
this is the chromatic number of $L(G)^2$, the square of the line graph. -/
noncomputable def strongChromaticIndex {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ (c : G.edgeSet → Fin k),
    ∀ (e₁ e₂ : G.edgeSet), c e₁ = c e₂ → e₁ ≠ e₂ →
      ∀ u ∈ (e₁ : Sym2 V), ∀ v ∈ (e₂ : Sym2 V), u ≠ v ∧ ¬G.Adj u v}

/-- Erdős–Nešetřil Strong Edge Coloring Conjecture (Erdős Problem 149) [ErNe85]:
For any finite graph $G$ with maximum degree $\Delta$,
$$
  \chi'_s(G) \leq \frac{5}{4} \Delta^2,
$$
i.e. the edge set of $G$ can be partitioned into at most $\frac{5}{4}\Delta^2$ strongly
independent edge sets. This bound is sharp: a blowup of $C_5$ with $\Delta = 2k$
requires exactly $5k^2 = \frac{5}{4}\Delta^2$ strong colors. -/
@[category research open, AMS 5]
theorem erdos_149 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (strongChromaticIndex G : ℝ) ≤ (5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2 := by
  sorry

end Erdos149
