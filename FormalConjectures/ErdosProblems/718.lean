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
# Erdős Problem 718

*Reference:* [erdosproblems.com/718](https://www.erdosproblems.com/718)

A conjecture of Erdős, Hajnal, and Mader. Dirac proved that every graph on $n$ vertices
with at least $2n - 2$ edges contains a subdivision of $K_4$, and conjectured that $3n - 5$
edges forces a subdivision of $K_5$.

Mader proved that $\geq 2^{\binom{r}{2}} \cdot n$ edges suffices.

[KoSz96] Komlós, J. and Szemerédi, E., _Topological cliques in graphs II_. Combinatorics,
Probability and Computing (1996), 5, 79–90.

[BoTh96] Bollobás, B. and Thomason, A., _Proof of a conjecture of Mader, Erdős and Hajnal
on topological complete subgraphs_. European J. Combin. (1998), 19, 883–887.
-/

open SimpleGraph

namespace Erdos718

/-- A graph $G$ contains a subdivision of $K_k$ if there exist $k$ distinct branch vertices
and internally vertex-disjoint paths between every pair of branch vertices. -/
def ContainsSubdivision {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (f : Fin k ↪ V)
    (paths : ∀ (i j : Fin k), i < j → G.Walk (f i) (f j)),
    (∀ i j (h : i < j), (paths i j h).IsPath) ∧
    (∀ i₁ j₁ (h₁ : i₁ < j₁) i₂ j₂ (h₂ : i₂ < j₂),
      (i₁, j₁) ≠ (i₂, j₂) →
      ∀ v, v ∈ (paths i₁ j₁ h₁).support.tail.dropLast →
           v ∉ (paths i₂ j₂ h₂).support.tail.dropLast) ∧
    (∀ i j (h : i < j) v,
      v ∈ (paths i j h).support.tail.dropLast →
      ∀ m : Fin k, v ≠ f m)

/--
**Erdős Problem 718** (Komlós–Szemerédi [KoSz96], Bollobás–Thomason [BoTh96]):

There exists an absolute constant $C > 0$ such that any graph on $n$ vertices
with at least $C \cdot r^2 \cdot n$ edges contains a subdivision of $K_r$.
-/
@[category research solved, AMS 5]
theorem erdos_718 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (n r : ℕ),
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (G.edgeFinset.card : ℝ) ≥ C * (r : ℝ) ^ 2 * (n : ℝ) →
          ContainsSubdivision G r := by
  sorry

end Erdos718
