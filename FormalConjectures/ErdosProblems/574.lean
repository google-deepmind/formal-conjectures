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
# Erdős Problem 574

*References:*
- [erdosproblems.com/574](https://www.erdosproblems.com/574)
- [ErSi82] Erdős, P. and Simonovits, M., *Compactness results in extremal graph theory*.
  Combinatorica (1982), 275-288.
- [LUW94b] Lazebnik, F. and Ustimenko, V. A. and Woldar, A. J., *Properties of certain families of
  $2k$-cycle-free graphs*. J. Combin. Theory Ser. B (1994), 293--298.
- [FNV06] Füredi, Zoltan and Naor, Assaf and Verstraëte, Jacques, *On the Turán number for the
  hexagon*. Adv. Math. (2006), 476--496.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos574

/-- The extremal number `ex(n; {C_{2k-1}, C_{2k}})`: the maximum number of edges of a graph on `n`
vertices containing neither a cycle of length `2k - 1` nor a cycle of length `2k`. -/
noncomputable def consecutiveCycleExtremalNumber (k n : ℕ) : ℕ := by
  classical
  exact Finset.sup {G : SimpleGraph (Fin n) |
    (SimpleGraph.cycleGraph (2 * k - 1)).Free G ∧ (SimpleGraph.cycleGraph (2 * k)).Free G}
    fun G ↦ G.edgeFinset.card

/--
Is it true that, for $k \geq 2$,
$$\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\}) = (1 + o(1)) (n/2)^{1 + \frac1k}?$$

A problem of Erdős and Simonovits [ErSi82]. This is false: it was first disproved for $k = 3$ and
$k = 5$ by Lazebnik, Ustimenko and Woldar [LUW94b], who constructed bipartite graphs containing no
$C_{2k}$ with $\left(\frac{k-1}{k^{1 + 1/k}} + o(1)\right) n^{1 + \frac1k}$ edges. An alternative
disproof for $k = 3$ is given by Füredi, Naor and Verstraëte [FNV06].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos574.lean#L343"]
theorem erdos_574 : answer(False) ↔
    ∀ k : ℕ, 2 ≤ k →
      (fun n : ℕ ↦ (consecutiveCycleExtremalNumber k n : ℝ)) ~[atTop]
        fun n : ℕ ↦ ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ)) := by
  sorry

end Erdos574
