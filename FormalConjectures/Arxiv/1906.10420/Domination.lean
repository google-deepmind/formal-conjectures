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
# Domination versus edge domination in regular graphs

Baste, Fürst, Henning, Mohr and Rautenbach define the edge domination number as the
minimum size of a maximal matching, denoted here by `SimpleGraph.saturationNumber`.

* [Baste et al., *Domination versus edge domination*, Conjecture 1](https://arxiv.org/pdf/1906.10420#page=1)
* [K. Afrasyab, *A 50-Vertex Cubic Counterexample*, Theorem 1](https://arxiv.org/html/2609.10783v1#Thmtheorem1)
* [C. Gupta, *Domination versus edge domination in regular graphs of degree at least seven*](https://arxiv.org/abs/2608.22498)
-/

@[expose] public section

open SimpleGraph

namespace Arxiv.«1906.10420»

/-- Every finite $d$-regular graph has a dominating set of size at most its minimum
maximal matching size. -/
def DominationBound (d : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsRegularOfDegree d →
    G.dominationNumber ≤ G.saturationNumber

open scoped Classical in
/-- Afrasyab's Theorem 1 gives a 50-vertex connected cubic graph with domination number 16
and edge domination number 15. -/
@[category research solved, AMS 5]
theorem cubic_counterexample : ∃ G : SimpleGraph (Fin 50), G.Connected ∧ G.IsRegularOfDegree 3 ∧
    G.dominationNumber = 16 ∧ G.saturationNumber = 15 := by
  sorry

/-- The universal inequality in Conjecture 1 of Baste et al. fails already at degree three. -/
@[category research solved, AMS 5]
theorem conjecture_one : ¬ (∀ d : ℕ, 1 ≤ d → DominationBound d) := by
  classical
  intro h
  obtain ⟨G, _, hreg, hdom, hsat⟩ := cubic_counterexample
  have hle := h 3 (by decide) 50 G hreg
  omega

/-- The cases $d = 4, 5, 6$ remain open. The inequality holds for $d \ge 7$ by Gupta. -/
@[category research open, AMS 5]
theorem conjecture_one.variants.degrees_four_to_six (d : ℕ) (hlo : 4 ≤ d) (hhi : d ≤ 6) :
    DominationBound d := by
  sorry

end Arxiv.«1906.10420»
