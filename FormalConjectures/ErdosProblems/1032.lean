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
# Erdős Problem 1032

*Reference:* [erdosproblems.com/1032](https://www.erdosproblems.com/1032)

Erdős asked whether there exists a constant $c > 0$ such that for arbitrarily large $n$,
there is a $4$-chromatic critical graph on $n$ vertices with minimum degree at least $c \cdot n$.

- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Mathematicae **16** (1993), 333–350.
- [Si72] Simonovits, M., _On colour-critical graphs_. Studia Scientiarum Mathematicarum
  Hungarica (1972), 67–81.
- [To72] Toft, B., _Two theorems on critical 4-chromatic graphs_. Studia Scientiarum
  Mathematicarum Hungarica (1972), 83–89.
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999), §3.60.

See also problems 917 and 944.
-/

open SimpleGraph

namespace Erdos1032

/--
A simple graph $G$ is $k$-critical if its chromatic number equals $k$ and for every
edge $e$, the graph obtained by deleting $e$ has chromatic number strictly less
than $k$.
-/
def IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧ ∀ e ∈ G.edgeSet, G.IsCriticalEdge e

/--
**Erdős Problem 1032** [Er93, p.341]:

Is there a constant $c > 0$ such that for arbitrarily large $n$, there exists
a $4$-chromatic critical graph on $n$ vertices with minimum degree at least $c \cdot n$?

Known results:
- Simonovits [Si72] and Toft [To72] independently constructed $4$-chromatic
  critical graphs with minimum degree $\gg n^{1/3}$.
- Dirac gave an example of a $6$-chromatic critical graph with minimum degree $> n/2$.
- This problem is also open for $5$-chromatic critical graphs.
-/
@[category research open, AMS 5]
theorem erdos_1032 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        IsCritical G 4 ∧ (G.minDegree : ℝ) ≥ c * (n : ℝ) := by
  sorry

/--
**Erdős Problem 1032 (5-chromatic variant)**:

Is there a constant $c > 0$ such that for arbitrarily large $n$, there exists
a $5$-chromatic critical graph on $n$ vertices with minimum degree at least $c \cdot n$?

This variant is also mentioned as open in [Er93, p.341].
-/
@[category research open, AMS 5]
theorem erdos_1032.variants.five_chromatic : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        IsCritical G 5 ∧ (G.minDegree : ℝ) ≥ c * (n : ℝ) := by
  sorry

end Erdos1032
