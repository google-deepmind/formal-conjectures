/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1079

*Reference:* [erdosproblems.com/1079](https://www.erdosproblems.com/1079)
-/

namespace Erdos1079

open SimpleGraph

/--
The extremal number (Turán number) $\mathrm{ex}(n; K_r)$ is the maximum number of edges
in a graph on $n$ vertices that does not contain a clique $K_r$.
-/
def turanNumber (n r : ℕ) : ℕ := sorry

/--
Let $r \geq 4$. If $G$ is a graph on $n$ vertices with at least $\mathrm{ex}(n; K_r)$ edges,
then $G$ contains a vertex with degree $d \gg_r n$ whose neighborhood contains at least
$\mathrm{ex}(d; K_{r-1})$ edges.

Erdős [Er75] says "if true this would be a nice generalisation of Turán's theorem".

This was proved by Bollobás and Thomason [BoTh81] (unless $G$ is itself the Turán graph).

[Er75] Erdős, P., _Problems and results in graph theory and combinatorial analysis_.
Proc. Fifth British Combinatorial Conference (Univ. Aberdeen, Aberdeen, 1975) (1976), 169-192.

[BoTh81] Bollobás, B. and Thomason, A., _Proof of a conjecture of Erdős_.
J. Combin. Theory Ser. B 30 (1981), 239-254.
-/
@[category research solved, AMS 05]
theorem erdos_1079 (r : ℕ) (hr : r ≥ 4) (n : ℕ) (G : SimpleGraph (Fin n))
    [Fintype (Fin n)] [DecidableRel G.Adj]
    (hG : G.edgeSet.ncard ≥ turanNumber n r) :
    ∃ (v : Fin n) (d : ℕ), G.degree v = d ∧
      (G.neighborSet v).toFinset.card ≥ turanNumber d (r - 1) := by
  sorry

/--
Bondy [Bo83b] showed that if $G$ has $> \mathrm{ex}(n; K_r)$ edges (strictly greater),
then the vertex can be chosen to be of maximum degree in $G$.

[Bo83b] Bondy, J. A., _A remark on two sufficient conditions for Hamilton cycles_.
Discrete Math. 22 (1978), 191-193.
-/
@[category research solved, AMS 05]
theorem erdos_1079.bondy_strengthening (r : ℕ) (hr : r ≥ 4) (n : ℕ) (G : SimpleGraph (Fin n))
    [Fintype (Fin n)] [DecidableRel G.Adj]
    (hG : G.edgeSet.ncard > turanNumber n r) :
    ∃ (v : Fin n), (∀ w, G.degree w ≤ G.degree v) ∧
      ∃ (d : ℕ), G.degree v = d ∧
      (G.neighborSet v).toFinset.card ≥ turanNumber d (r - 1) := by
  sorry

end Erdos1079
