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

import FormalConjecturesUtil

/-!
# Seymour's second neighbourhood conjecture (1990)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Seymour%27s_second_neighborhood_conjecture)
* [DL95] Dean, N. and Latka, B. J. (1995). "Squaring the tournament — an open problem."
  *Congr. Numer.* 109, pp. 73--80.
* [Fi96] Fisher, D. C. (1996). "Squaring a tournament: a proof of Dean's conjecture."
  *J. Graph Theory* 23, pp. 43--48.
* [HT00] Havet, F. and Thomassé, S. (2000). "Median orders of tournaments: a tool for the
  second neighborhood problem and Sumner's conjecture." *J. Graph Theory* 35, pp. 244--256.
* [KL01] Kaneko, Y. and Locke, S. C. (2001). "The minimum degree approach for Paul Seymour's
  distance 2 conjecture." *Congr. Numer.* 148, pp. 201--206.
* [CSY03] Chen, G., Shen, J. and Yuster, R. (2003). "Second neighborhood via first neighborhood
  in digraphs." *Ann. Comb.* 7, pp. 15--20.
-/

open Finset

namespace SeymourSecondNeighborhoodConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A digraph is an **oriented graph** if it has no loops and no pair of opposite arcs. -/
def IsOriented (D : Digraph V) : Prop :=
  (∀ v, ¬ D.Adj v v) ∧ ∀ u v, D.Adj u v → ¬ D.Adj v u

/-- The (first) out-neighbourhood `N⁺(v)` of `v`: the vertices `w` with an arc `v → w`. -/
def outNeighbors (D : Digraph V) [DecidableRel D.Adj] (v : V) : Finset V :=
  univ.filter fun w => D.Adj v w

/-- The **second out-neighbourhood** `N⁺⁺(v)` of `v`: the vertices at directed distance exactly
`2` from `v`, i.e. those `w ≠ v` that are not out-neighbours of `v` but are out-neighbours of
some out-neighbour of `v`. -/
def secondOutNeighbors (D : Digraph V) [DecidableRel D.Adj] (v : V) : Finset V :=
  univ.filter fun w => w ≠ v ∧ ¬ D.Adj v w ∧ ∃ u, D.Adj v u ∧ D.Adj u w

/--
**Seymour's second neighbourhood conjecture (1990).**

Every finite oriented graph with at least one vertex has a vertex $v$ whose second
out-neighbourhood is at least as large as its first: $|N^{++}(v)| \ge |N^{+}(v)|$.
-/
@[category research open, AMS 5]
theorem seymour_second_neighborhood_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (D : Digraph V) [DecidableRel D.Adj],
      IsOriented D → ∃ v, (outNeighbors D v).card ≤ (secondOutNeighbors D v).card := by
  sorry

/--
**Tournaments (Dean's conjecture; proved by Fisher 1996, and again by Havet–Thomassé 2000).**

Every tournament has a vertex whose second out-neighbourhood is at least as large as its first.

*References:* [DL95], [Fi96], [HT00].
-/
@[category research solved, AMS 5]
theorem seymour_second_neighborhood_conjecture.variants.tournament
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (D : Digraph V) [DecidableRel D.Adj]
    (hD : D.IsTournament) :
    ∃ v, (outNeighbors D v).card ≤ (secondOutNeighbors D v).card := by
  sorry

/--
**Kaneko–Locke (2001): minimum out-degree at most `6`.**

The conjecture holds for every oriented graph whose minimum out-degree is at most $6$.

*Reference:* [KL01].
-/
@[category research solved, AMS 5]
theorem seymour_second_neighborhood_conjecture.variants.min_outdegree_le_six
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (D : Digraph V) [DecidableRel D.Adj]
    (hD : IsOriented D) (hdeg : ∃ v, (outNeighbors D v).card ≤ 6) :
    ∃ v, (outNeighbors D v).card ≤ (secondOutNeighbors D v).card := by
  sorry

/--
**Chen–Shen–Yuster (2003): a constant-factor version.**

Every oriented graph has a vertex $v$ with $|N^{++}(v)| \ge \gamma\,|N^{+}(v)|$, where
$\gamma = 0.657\ldots$ is the unique real root of $2x^3 + x^2 - 1 = 0$.

*Reference:* [CSY03].
-/
@[category research solved, AMS 5]
theorem seymour_second_neighborhood_conjecture.variants.chen_shen_yuster
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (D : Digraph V) [DecidableRel D.Adj]
    (hD : IsOriented D) (γ : ℝ) (hγ : 2 * γ ^ 3 + γ ^ 2 - 1 = 0) (hγ₀ : 0 < γ) :
    ∃ v, γ * (outNeighbors D v).card ≤ (secondOutNeighbors D v).card := by
  sorry

/--
**A vertex of out-degree `0` witnesses the conjecture.**

If some vertex has no out-neighbours (a *sink*) then the inequality holds at that vertex
trivially. In particular the conjecture holds for every oriented graph with a sink, e.g. every
acyclic oriented graph.
-/
@[category test, AMS 5]
theorem seymour_second_neighborhood_conjecture.variants.sink
    {V : Type} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (v : V) (hv : ∀ w, ¬ D.Adj v w) :
    (outNeighbors D v).card ≤ (secondOutNeighbors D v).card := by
  have h : outNeighbors D v = ∅ := by
    ext w
    simp [outNeighbors, hv w]
  rw [h, Finset.card_empty]
  exact Nat.zero_le _

end SeymourSecondNeighborhoodConjecture
