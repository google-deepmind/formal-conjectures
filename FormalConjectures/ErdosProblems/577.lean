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
# Erdős Problem 577

*References:*
- [erdosproblems.com/577](https://www.erdosproblems.com/577)
- [Wa10] Wang, Hong, *Proof of the Erdős-Faudree conjecture on quadrilaterals*.
  Graphs Combin. (2010), 833-877. [DOI](https://doi.org/10.1007/s00373-010-0948-3)
-/

@[expose] public section

open SimpleGraph

namespace Erdos577

open scoped Classical in
set_option linter.style.formal_proof_palomar false in
/--
If $G$ is a graph with $4k$ vertices and minimum degree at least $2k$ then $G$ contains $k$
vertex-disjoint $4$-cycles.

A conjecture of Erdős and Faudree. Proved by Wang [Wa10].
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos577.lean"]
theorem erdos_577 (k : ℕ) (G : SimpleGraph (Fin (4 * k)))
    (hG : 2 * k ≤ G.minDegree) :
    ∃ cycles : Fin k → (cycleGraph 4).Copy G,
      Pairwise fun i j => Disjoint (Set.range (fun v => cycles i v))
        (Set.range (fun v => cycles j v)) := by
  sorry

end Erdos577
