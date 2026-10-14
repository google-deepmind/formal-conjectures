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
# Written on the Wall II - Conjecture 271

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc,
  Conjecture 271, 23 February 2007](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Total domination and distance between maximum-degree
  vertices, 12 October 2026](https://github.com/google-deepmind/formal-conjectures/issues/7235)

Gebendorfer's proof derives the classical diameter estimate of DeLaVina, Liu,
Pepper, Waller and West, Some conjectures of Graffiti.pc on total domination
(2007), Lemma 3. The linked Lean proof includes that derivation.
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture271

open SimpleGraph

/--
Every finite simple connected graph with at least two vertices has total
domination number at least $\lceil\sqrt{2d_M}\rceil$, where $M$ is its
maximum-degree vertex set and $d_M=\max_{u,v\in M}\operatorname{dist}_G(u,v)$.

Distances are measured in $G$, and equal pairs are allowed. Thus $d_M=0$ when
$M$ is a singleton. The maximum-degree set is nonempty. Nontriviality excludes
the one-vertex graph, which has no total dominating set.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/5a980fa4e0305f3097dd49fc537fc26eff7f8472/Proofs/WOWII271Proof.lean"]
theorem conjecture271 {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    let M := Finset.univ.filter fun v => G.degree v = G.maxDegree
    let dM := (M ×ˢ M).sup fun p => G.dist p.1 p.2
    ⌈Real.sqrt (2 * dM : ℝ)⌉₊ ≤ G.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture271

