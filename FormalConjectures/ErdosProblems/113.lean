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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 113

*References:*
- [erdosproblems.com/113](https://www.erdosproblems.com/113)
- [ErSi84] Erdős, P. and Simonovits, M., *Cube-supersaturated graphs and related problems*.
  Progress in graph theory (Waterloo, Ont., 1982) (1984), 203-218.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [Ja23b] Janzer, Oliver, *Disproof of a conjecture of Erdős and Simonovits on the Turán number
  of graphs with minimum degree 3*. Int. Math. Res. Not. IMRN (2023), 8478--8494.
-/

@[expose] public section

open Filter Asymptotics SimpleGraph

namespace Erdos113

/--
If $G$ is bipartite then $\mathrm{ex}(n;G)\ll n^{3/2}$ if and only $G$ is $2$-degenerate, that
is, $G$ contains no induced subgraph with minimal degree at least 3.

Conjectured by Erdős and Simonovits [ErSi84]. Erdős first offered \$250 for a proof and \$100 for
a counterexample, but in [Er93] offered \$500 for a counterexample. Disproved by Janzer [Ja23b]
who constructed, for any $\epsilon>0$, a $3$-regular bipartite graph $H$ such that
$$\mathrm{ex}(n;H)\ll n^{\frac{4}{3}+\epsilon}.$$

See also [146](https://www.erdosproblems.com/146) and [147](https://www.erdosproblems.com/147).

The linked formal proof refutes the "only if" direction via Janzer's construction.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos113.lean#L4902"]
theorem erdos_113 : answer(False) ↔ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsBipartite →
    (((fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) ↔
      G.IsDegenerate 2) := by
  sorry

end Erdos113
