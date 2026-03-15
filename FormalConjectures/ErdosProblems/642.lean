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
# Erdős Problem 642

*Reference:* [erdosproblems.com/642](https://www.erdosproblems.com/642)

Let $f(n)$ be the maximal number of edges in a graph on $n$ vertices such that
all cycles have more vertices than chords. Is it true that $f(n) \ll n$?

A chord is an edge between two vertices of the cycle which are not consecutive
in the cycle. A problem of Hamburger and Szegedy.

Chen, Erdős, and Staton [CES96] proved $f(n) \ll n^{3/2}$. Draganić, Methuku,
Munhá Correia, and Sudakov [DMMS24] improved this to $f(n) \ll n(\log n)^8$.

[CES96] Chen, G., Erdős, P., and Staton, W., _Proof of a conjecture of
Bollobás on nested cycles_. J. Combin. Theory Ser. B (1996), 38–43.

[DMMS24] Draganić, N., Methuku, A., Munhá Correia, D., and Sudakov, B.,
_Cycles with many chords_. Random Structures & Algorithms (2024), 3–16.

[Er97d] Erdős, P., _Some old and new problems in various branches of
combinatorics_. Discrete Math. (1997).
-/

open SimpleGraph

namespace Erdos642

variable {V : Type*} [Fintype V] [DecidableEq V]
         {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The number of chords of a walk in a graph. A chord is an edge of $G$
connecting two vertices that appear in the walk's support but is not
itself an edge traversed by the walk. -/
noncomputable def numChords {u v : V} (p : G.Walk u v) : ℕ :=
  (G.edgeFinset.filter (fun e =>
    (∀ w, w ∈ e → w ∈ p.support.toFinset) ∧ e ∉ p.edges.toFinset)).card

/--
Erdős Problem 642 [CES96][Er97d]:

There exists a constant $C$ such that for all $n$, every graph $G$ on $n$
vertices in which every cycle has strictly more vertices than chords has at
most $C \cdot n$ edges.
-/
@[category research open, AMS 5]
theorem erdos_642 :
    answer(sorry) ↔
      ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle →
          p.support.toFinset.card > numChords p) →
        G.edgeFinset.card ≤ C * n := by
  sorry

end Erdos642
