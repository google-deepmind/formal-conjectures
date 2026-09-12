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
# Erdős Problem 1091

*References:*
- [erdosproblems.com/1091](https://www.erdosproblems.com/1091)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant, *Short proofs in
  combinatorics, probability, and number theory II*. arXiv:2604.06609 (2026).
- [La79] Larson, Jean A., *Some graphs with chromatic number three*. J. Combin. Theory Ser. B
  (1979), 317--322.
- [Vo82] Voss, Heinz-Jürgen, *Graphs having circuits with at least two chords*. J. Combin. Theory
  Ser. B (1982), 264--285.
-/

namespace Erdos1091

open SimpleGraph Filter

variable {V : Type*}

/--
The diagonals (also called chords) of a cycle: edges of `G` that join two vertices of the cycle
but are not themselves edges of the cycle.
-/
def cycleDiagonals {G : SimpleGraph V} (c : G.Cycle) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ (∀ v ∈ e, v ∈ c.walk.support) ∧ e ∉ c.edges}

/-- `G` contains an odd cycle with at least `k` diagonals. -/
def HasOddCycleWithDiagonals (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : G.Cycle, Odd c.length ∧ k ≤ (cycleDiagonals c).encard

/-- Every subgraph of `G` on at most `r` vertices has chromatic number at most `3`. -/
def IsLocallyThreeColorable (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ H : G.Subgraph, H.verts.encard ≤ r → H.coe.chromaticNumber ≤ 3

/-- A cut vertex of `G` is a vertex whose deletion strictly increases the number of connected
components. -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  Cardinal.mk G.ConnectedComponent < Cardinal.mk (G.induce {v}ᶜ).ConnectedComponent

/--
Let $G$ be a $K_4$-free graph with chromatic number $4$. Must $G$ contain an odd cycle with at
least two diagonals?

The first question was solved in the affirmative by Voss [Vo82].
-/
@[category research solved, AMS 5]
theorem erdos_1091.parts.i : answer(True) ↔
    ∀ {V : Type*} (G : SimpleGraph V),
      G.CliqueFree 4 → G.chromaticNumber = 4 → HasOddCycleWithDiagonals G 2 := by
  sorry

/--
More generally, is there some $f(r)\to \infty$ such that every graph with chromatic number $4$,
in which every subgraph on $\leq r$ vertices has chromatic number $\leq 3$, contains an odd cycle
with at least $f(r)$ diagonals?

An internal OpenAI model (see [APSSV26b]) has provided a negative answer to the second question:
for every $m\geq 1$ there is a graph $G$, with no $K_4$, on $\asymp m$ many vertices with
chromatic number $4$, such that every proper subgraph has chromatic number $\leq 3$, and every
cycle in $G$ contains at most $10$ diagonals.
-/
@[category research solved, AMS 5]
theorem erdos_1091.parts.ii : answer(False) ↔
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ (r : ℕ) {V : Type*} (G : SimpleGraph V),
        G.chromaticNumber = 4 → IsLocallyThreeColorable G r →
          HasOddCycleWithDiagonals G (f r) := by
  sorry

/--
Erdős originally asked about the existence of just one diagonal, which is true, and was proved by
Larson [La79].
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.one_diagonal {V : Type*} (G : SimpleGraph V)
    (hK : G.CliqueFree 4) (hχ : G.chromaticNumber = 4) :
    HasOddCycleWithDiagonals G 1 := by
  sorry

/--
In fact Larson proved the following stronger conjecture of Bollobás and Erdős: if $G$ is a
$K_4$-free graph containing no odd cycle with a diagonal then either $G$ is bipartite, or $G$
contains a cut vertex, or $G$ contains a vertex with degree $\leq 2$.
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.bollobas_erdos {V : Type*} (G : SimpleGraph V)
    (hK : G.CliqueFree 4) (h : ¬ HasOddCycleWithDiagonals G 1) :
    G.IsBipartite ∨ (∃ v, IsCutVertex G v) ∨ (∃ v, (G.neighborSet v).encard ≤ 2) := by
  sorry

/--
The pentagonal wheel shows that three diagonals are not guaranteed.
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.three_diagonals :
    ∃ (V : Type*) (G : SimpleGraph V),
      G.CliqueFree 4 ∧ G.chromaticNumber = 4 ∧ ¬ HasOddCycleWithDiagonals G 3 := by
  sorry

/--
An internal OpenAI model (see [APSSV26b]) has provided a negative answer to the second question:
for every $m\geq 1$ there is a graph $G$, with no $K_4$, on $\asymp m$ many vertices with
chromatic number $4$, such that every proper subgraph has chromatic number $\leq 3$, and every
cycle in $G$ contains at most $10$ diagonals.
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.counterexample (m : ℕ) (hm : 1 ≤ m) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      m ≤ n ∧ G.CliqueFree 4 ∧ G.chromaticNumber = 4 ∧
        (∀ H : G.Subgraph, H ≠ ⊤ → H.coe.chromaticNumber ≤ 3) ∧
        (∀ c : G.Cycle, (cycleDiagonals c).encard ≤ 10) := by
  sorry

end Erdos1091
