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
# Erdős Problem 580

If at least half the vertices of an $n$-vertex graph have degree at least $n/2$, must the graph
contain every tree on at most $n/2$ vertices as a subgraph?

This problem has status **DECIDABLE** — resolved up to a finite check, since Zhao [Zh11] proved the
conjecture for all sufficiently large $n$.

*Reference:* [erdosproblems.com/580](https://www.erdosproblems.com/580)

[EFLS95] Erdős, P., Füredi, Z., Loebl, M., and Sós, V.T.

[AKS95] Ajtai, M., Komlós, J., and Szemerédi, E., _On a conjecture of Loebl_.
Graph theory, combinatorics, and algorithms, Vol. 1, 2 (Kalamazoo, MI, 1992), 1995, 1135–1146.

[Zh11] Zhao, Y., _Proof of the (n/2–n/2–n/2) conjecture for large n_.
Electronic Journal of Combinatorics **18** (2011), Paper 27, 61 pp.
-/

open SimpleGraph Finset

namespace Erdos580

/--
Erdős-Füredi-Loebl-Sós Conjecture (Problem 580):
Let $G$ be a graph on $n$ vertices such that at least $n/2$ vertices have degree at
least $n/2$. Must $G$ contain every tree on at most $n/2$ vertices?

Conjectured by Erdős, Füredi, Loebl, and Sós [EFLS95].
Ajtai, Komlós, and Szemerédi [AKS95] proved an asymptotic version.
Zhao [Zh11] proved the conjecture for all sufficiently large $n$.
-/
@[category research open, AMS 5]
theorem erdos_580 : answer(sorry) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      n / 2 ≤ (Finset.univ.filter (fun v => n / 2 ≤ G.degree v)).card →
      ∀ (k : ℕ) (T : SimpleGraph (Fin k)) [DecidableRel T.Adj],
        k ≤ n / 2 → T.IsTree → Nonempty (T ↪g G) := by
  sorry

/--
Komlós–Sós Conjecture (generalization of Problem 580):
If at least $n/2$ vertices of an $n$-vertex graph $G$ have degree at least $k$, then $G$ contains
every tree with at most $k+1$ vertices (equivalently, at most $k$ edges).

Problem 580 is the special case $k = \lfloor n/2 \rfloor$ of this conjecture.
-/
@[category research open, AMS 5]
theorem erdos_580_komlos_sos : answer(sorry) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ (k : ℕ),
      n / 2 ≤ (Finset.univ.filter (fun v => k ≤ G.degree v)).card →
      ∀ (m : ℕ) (T : SimpleGraph (Fin m)) [DecidableRel T.Adj],
        m ≤ k + 1 → T.IsTree → Nonempty (T ↪g G) := by
  sorry

end Erdos580
