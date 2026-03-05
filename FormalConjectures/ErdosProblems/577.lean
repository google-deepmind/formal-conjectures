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
# Erdős Problem 577

*Reference:* [erdosproblems.com/577](https://www.erdosproblems.com/577)

A conjecture of Erdős and Faudree [Er90c]. Proved by Wang [Wa10].

[Er90c] Erdős, P., Some of my favourite problems in various branches of combinatorics,
Matematiche (Catania) 45 (1990), 59-73.

[Wa10] Wang, H., Proof of the Erdős-Faudree conjecture on quadrilaterals, Graphs and
Combinatorics 26 (2010), 833-877.
-/

open SimpleGraph

namespace Erdos577

/-- Four vertices form a $4$-cycle in $G$: they are pairwise distinct and
adjacent in cyclic order $a \sim b \sim c \sim d \sim a$. -/
def IsFourCycle {V : Type*} (G : SimpleGraph V) (a b c d : V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- The set of vertices in a $4$-tuple. -/
def fourCycleVertices {V : Type*} (t : V × V × V × V) : Set V :=
  let (a, b, c, d) := t; {a, b, c, d}

/--
Erdős Problem 577 [Er90c]:

If $G$ is a graph with $4k$ vertices and minimum degree at least $2k$ then $G$
contains $k$ vertex-disjoint $4$-cycles.

A conjecture of Erdős and Faudree. Proved by Wang [Wa10].
-/
@[category research solved, AMS 5]
theorem erdos_577 :
    ∀ (k : ℕ)
      (G : SimpleGraph (Fin (4 * k))) (dG : DecidableRel G.Adj),
      haveI := dG;
      (∀ v : Fin (4 * k), 2 * k ≤ G.degree v) →
      ∃ cycles : Fin k → Fin (4 * k) × Fin (4 * k) × Fin (4 * k) × Fin (4 * k),
        (∀ i, let (a, b, c, d) := cycles i; IsFourCycle G a b c d) ∧
        (∀ i j, i ≠ j →
          Disjoint (fourCycleVertices (cycles i)) (fourCycleVertices (cycles j))) := by
  sorry

end Erdos577
