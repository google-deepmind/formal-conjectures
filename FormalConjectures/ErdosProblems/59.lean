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
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

/-!
# Erdős Problem 59

*Reference:* [erdosproblems.com/59](https://www.erdosproblems.com/59)

Is it true that for every graph $G$, the number of labeled $G$-free graphs on $n$ vertices
is at most $2^{(1+o(1)) \cdot \operatorname{ex}(n; G)}$? Disproved: the answer is no for
$G = C_6$ (Morris and Saxton [MoSa16]). Erdős, Frankl, and Rödl [EFR86] proved the
answer is yes when $G$ is not bipartite.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467–478.

[Er93, p.335] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae (1993), 333–350.

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.

[Va99, 3.56] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics", Budapest, July 1999 (1999).

[EFR86] Erdős, P., Frankl, P., Rödl, V., _The asymptotic number of graphs not containing
a fixed subgraph and a problem for hypergraphs having no exponent_. Graphs and
Combinatorics (1986), 113–121.

[MoSa16] Morris, R., Saxton, D., _The number of $C_{2\ell}$-free graphs_. Adv. Math. (2016),
534–580.
-/

open SimpleGraph

namespace Erdos59

/-- The number of labeled simple graphs on $n$ vertices that do not contain $H$ as a subgraph. -/
noncomputable def countHFreeGraphs {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  Nat.card {F : SimpleGraph (Fin n) // H.Free F}

/--
Erdős Problem 59 [Er90, Er93, p.335, Er97c, Va99, 3.56]:

Is it true that, for every graph $G$, the number of labeled graphs on $n$ vertices that
contain no copy of $G$ is at most $2^{(1+o(1)) \cdot \operatorname{ex}(n; G)}$?

That is, for every $\varepsilon > 0$, for all sufficiently large $n$:
$$\#\{\text{$G$-free graphs on $[n]$}\} \leq 2^{(1+\varepsilon) \cdot \operatorname{ex}(n; G)}$$

This was DISPROVED: the answer is no for $G = C_6$ (the 6-cycle).
Erdős, Frankl, and Rödl [EFR86] proved the answer is yes when $G$ is not bipartite.
Morris and Saxton [MoSa16] showed there are at least $2^{(1+c) \cdot \operatorname{ex}(n; C_6)}$
such graphs for infinitely many $n$, for some constant $c > 0$.
-/
@[category research solved, AMS 5]
theorem erdos_59 : answer(False) ↔
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (countHFreeGraphs H n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (extremalNumber n H : ℝ)) := by
  sorry

/--
Morris–Saxton weaker conjecture: for every graph $G$, the number of labeled $G$-free graphs
on $n$ vertices is at most $2^{O(\operatorname{ex}(n; G))}$. That is, there exists a constant
$C$ (depending on $G$) such that the count is at most $2^{C \cdot \operatorname{ex}(n; G)}$
for all sufficiently large $n$. This weaker bound is conjectured to hold even though the
original conjecture (with $1 + o(1)$ in the exponent) was disproved for $C_6$.
-/
@[category research open, AMS 5]
theorem erdos_59_weakened : answer(sorry) ↔
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
    ∃ (C : ℝ) (_ : 0 < C) (N : ℕ), ∀ n : ℕ, N ≤ n →
      (countHFreeGraphs H n : ℝ) ≤ (2 : ℝ) ^ (C * (extremalNumber n H : ℝ)) := by
  sorry

/--
The $C_4$ case of Erdős Problem 59 [Va99, 3.56]: does the original bound
$2^{(1+o(1)) \cdot \operatorname{ex}(n; C_4)}$ hold for the number of labeled $C_4$-free
graphs on $n$ vertices? This remains open even though the general conjecture was
disproved for $C_6$.
-/
@[category research open, AMS 5]
theorem erdos_59_C4 : answer(sorry) ↔
    ∀ (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj],
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (countHFreeGraphs H n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (extremalNumber n H : ℝ)) := by
  sorry

end Erdos59
