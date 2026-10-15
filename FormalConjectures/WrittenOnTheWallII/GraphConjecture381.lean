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
# Written on the Wall II — Conjecture 381

*References:*
- [E. DeLaVina, Written on the Wall II](https://cms.uhd.edu/faculty/delavinae/research/wowII/open.html)
- [J. J. Gebendorfer, Support neighborhoods and total domination: a proof of Written on the Wall II 381, 14 October 2026](https://github.com/google-deepmind/formal-conjectures/issues/7334)
-/

@[expose] public section
namespace WrittenOnTheWallII.GraphConjecture381
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def neighbors (S : Finset V) : Finset V :=
  univ.filter fun v => ∃ s ∈ S, G.Adj v s

def isolates (S : Finset V) : Finset V :=
  S.filter fun v => ∀ w ∈ S, ¬ G.Adj v w

def supports : Finset V := univ.filter fun s => ∃ p, G.degree p = 1 ∧ G.Adj s p

def supportDegree : ℕ := (supports G).sup (fun v => G.degree v)

/-- For every finite simple tree $T$ of order greater than two,
$\gamma_t(T)\ge i(T[N(S)])/(b-1)$, where $S$ is the full support set,
$N(S)$ is the union of open neighborhoods, $i$ counts isolated vertices,
and $b$ is the largest ambient degree of a support. The neighborhood may meet
$S$. These trees have supports and $b\ge2$, so the denominator is positive.
The exact rational comparison is equivalent to the real-valued inequality.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
"https://github.com/RhudeJJJJ/formal-conjectures/blob/9bf6a9ca86495a241446cce10e013a8794af666f/Proofs/WOWII381Proof.lean"]
theorem conjecture381 : ∀ (W : Type) [Fintype W] [DecidableEq W]
      (T : SimpleGraph W) [DecidableRel T.Adj], T.IsTree → 2 < Fintype.card W →
      ((isolates T (neighbors T (supports T))).card : ℚ) /
        ((supportDegree T : ℚ) - 1) ≤ T.totalDominationNumber := by
  sorry

end WrittenOnTheWallII.GraphConjecture381
