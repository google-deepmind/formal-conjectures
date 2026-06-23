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
# TxGraffiti Conjecture 4: the saturation number versus the harmonic index

*Reference:* [arxiv/2507.17780](https://arxiv.org/abs/2507.17780)
**In Reverie Together: Ten Years of Mathematical Discovery with a Machine
Collaborator** by *Randy Davila, Boris Brimkov, Ryan Pepper*

TxGraffiti is an automated conjecturing program, a successor of Fajtlowicz's
*Graffiti* and DeLaViña's *Graffiti.pc*. Conjecture 4 in the cited collection
asserts a bound between two graph invariants:

* the *saturation number* $\mu^*(G)$ (`SimpleGraph.saturationNumber`), the
  minimum number of edges in a maximal matching of $G$;
* the *harmonic index* $H(G)$ (`SimpleGraph.harmonicIndex`),
  $\sum_{uv \in E(G)} 2 / (\deg u + \deg v)$.

The conjecture is **false**. It was first refuted by Bıyıkoğlu, who exhibited a
family of counterexamples — a disjoint union of edges joined to an independent
set — with unbounded ratio $\mu^*/H$. That the smallest counterexample has
order $9$, namely the friendship graph $F_4$ formalised below, and that the
windmill family has an exact limiting ratio, are established in Gupta.

*References:*
- [A Note on the TxGraffiti Conjecture about Harmonic Index and Minimum Maximal
  Matching Number](https://doi.org/10.46793/match.96-3.28425), Türker Bıyıkoğlu,
  *MATCH Commun. Math. Comput. Chem.* **96** (2026), no. 3, 1097–1099 — the
  first refutation.
- [The saturation number is not bounded by the harmonic
  index](https://arxiv.org/abs/2606.15761), C. Gupta — the order-$9$
  minimality of $F_4$ (formalised below) and the exact windmill limit.
-/

open SimpleGraph

namespace Arxiv.«2507.17780»

/-- The friendship graph $F_4$: a hub vertex $0$ joined to four triangles, whose
rims are the pairs $\{1,2\}, \{3,4\}, \{5,6\}, \{7,8\}$. It has $12$ edges on
$9$ vertices ($8$ spokes and $4$ rim edges). -/
def friendshipF4 : SimpleGraph (Fin 9) := fromEdgeSet {
  s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(0, 6), s(0, 7), s(0, 8),
  s(1, 2), s(3, 4), s(5, 6), s(7, 8) }

instance : DecidableRel friendshipF4.Adj := by unfold friendshipF4; infer_instance

/--
TxGraffiti [Conjecture 4](https://arxiv.org/abs/2507.17780):
for every nontrivial connected graph $G$, the saturation number is at most
the harmonic index, $\mu^*(G) \le H(G)$.

This conjecture is **FALSE**.

**Counterexample.**
The friendship graph $F_4$ (`friendshipF4`) is connected and nontrivial, with
$\mu^*(F_4) = 4$ and $H(F_4) = 18/5$. Indeed the four rim edges
$\{1,2\}, \{3,4\}, \{5,6\}, \{7,8\}$ form a maximal matching of size $4$, and
no maximal matching is smaller, so $\mu^*(F_4) = 4$; the eight spokes
contribute $2/(8+2) = 1/5$ each and the four rim edges contribute
$2/(2+2) = 1/2$ each, giving $H(F_4) = 8 \cdot 1/5 + 4 \cdot 1/2 = 18/5$.
Since $4 > 18/5$, the bound fails.

More generally the friendship graphs $F_k$ satisfy $\mu^*(F_k) = k$ and
$H(F_k) = 2k/(k+1) + k/2$, so the conjecture fails for every $k \ge 4$. An
exhaustive search confirms that $F_4$ is the smallest counterexample
(order $9$). The unbounded separation was first shown by Bıyıkoğlu, whose
family of edges joined to an independent set makes $\mu^*/H$ arbitrarily
large; the windmill generalisation and its exact limit appear in
[arXiv:2606.15761](https://arxiv.org/abs/2606.15761).
-/
@[category research solved, AMS 5]
theorem txGraffitiConjecture4 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (_hConn : G.Connected),
      (G.saturationNumber : ℚ) ≤ G.harmonicIndex := by
  refine iff_of_false (by simp) (fun h => ?_)
  have key := h (Fin 9) friendshipF4 (by native_decide)
  rw [friendshipF4.sat_num_eq_computable] at key
  revert key
  native_decide

end Arxiv.«2507.17780»
