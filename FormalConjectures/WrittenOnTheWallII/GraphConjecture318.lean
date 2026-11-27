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
# Written on the Wall II - Conjecture 318

Graffiti.pc Conjecture 318 was announced on March 4, 2007, in Ermelinda DeLaViña’s
[*Written on the Wall II*](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html).
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture318

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

set_option linter.style.formal_proof_palomar false in
/-- Let $G$ be a finite connected simple graph on at least two vertices. If the number
of missing edges is at most the largest number of vertices at even distance from a vertex,
then $G$ is well totally dominated. Distance zero counts as even. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/formal-conjectures/blob/f0d853270e680e6577d14e949f3ceb8ceb0e8fbb/Proofs/GraphConjecture318.lean#L39-L42"]
theorem conjecture318 [Nontrivial V] (hG : G.Connected)
    (h : Gᶜ.edgeFinset.card ≤ Finset.univ.sup G.distEven) : G.IsWellTotallyDominated := by
  sorry

end WrittenOnTheWallII.GraphConjecture318
