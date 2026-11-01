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
# Erdős Problem 1032

*References:*
- [erdosproblems.com/1032](https://www.erdosproblems.com/1032)
- [Er93] Erdős, P., *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. 16 (1993), 333-350.
- [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
- [Di52] Dirac, G. A., *A property of $4$-chromatic graphs and some remarks on critical graphs*.
  J. London Math. Soc. 27 (1952), 85-92.
- [Si72] Simonovits, M., *On colour-critical graphs*. Studia Sci. Math. Hungar. 7 (1972), 67-81.
- [To72] Toft, B., *Two theorems on critical $4$-chromatic graphs*. Studia Sci. Math. Hungar. 7
  (1972), 83-89.
- [Ma15] Markström, K. (ed.), *Problem collection from the IML programme: Graphs, Hypergraphs,
  and Computing*. [arXiv:1511.00270](https://arxiv.org/abs/1511.00270) (2015). Problem 5.1
  (M. Simonovits).

See also [erdosproblems.com/917](https://www.erdosproblems.com/917) and
[erdosproblems.com/944](https://www.erdosproblems.com/944).
-/

@[expose] public section

open Filter

namespace Erdos1032

/-- A graph `G` is `k`-critical if it has chromatic number `k` and every proper subgraph has
chromatic number less than `k`. For a finite graph a proper subgraph misses a vertex or an edge, so
this holds iff `G.IsCritical k` (deleting any vertex lowers the chromatic number) and deleting any
edge lowers the chromatic number.

The definition on the problem page uses only the edge condition. This would allow isolated
vertices, but a minimum degree $\geq cn$ with $c > 0$ excludes them, so the two notions agree in
the statements below. -/
def IsKCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.IsCritical k ∧ ∀ e ∈ G.edgeSet, G.IsCriticalEdge e

open scoped Classical in
/--
We say that a graph is $4$-chromatic critical if it has chromatic number $4$, and removing any edge
decreases the chromatic number to $3$.

Is there, for arbitrarily large $n$, a $4$-chromatic critical graph on $n$ vertices with minimum
degree $\gg n$?

This is a question of Erdős [Er93, p. 341] (see also [Va99, 3.60]). We read $\gg n$ as
$\geq cn$ for a fixed constant $c > 0$.
-/
@[category research open, question, AMS 5]
theorem erdos_1032 :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n), IsKCritical G 4 ∧ c * (n : ℝ) ≤ (G.minDegree : ℝ) := by
  sorry

open scoped Classical in
/--
Is there, for arbitrarily large $n$, a $5$-chromatic critical graph on $n$ vertices with minimum
degree $\gg n$?

This problem is also open for $5$-chromatic critical graphs.
-/
@[category research open, question, AMS 5]
theorem erdos_1032.variants.five :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n), IsKCritical G 5 ∧ c * (n : ℝ) ≤ (G.minDegree : ℝ) := by
  sorry

open scoped Classical in
/--
Dirac gave an example of a $6$-chromatic critical graph with minimum degree $>n/2$.

Dirac's graphs join two disjoint odd cycles of length $n/2$ [Di52], [Ma15]. Here we state that
there are such graphs for infinitely many $n$.
-/
@[category research solved, AMS 5]
theorem erdos_1032.variants.dirac_six :
    ∃ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n), IsKCritical G 6 ∧ (n : ℝ) / 2 < (G.minDegree : ℝ) := by
  sorry

open scoped Classical in
/--
Simonovits [Si72] and Toft [To72] independently constructed $4$-chromatic critical graphs with
minimum degree $\gg n^{1/3}$.

We state this as in [Ma15, Problem 5.1]: there are $4$-critical graphs on $n$ vertices with minimum
degree at least $c n^{1/3}$ for infinitely many $n$, for a fixed constant $c > 0$.
-/
@[category research solved, AMS 5]
theorem erdos_1032.variants.simonovits_toft :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n),
        IsKCritical G 4 ∧ c * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (G.minDegree : ℝ) := by
  sorry

end Erdos1032
