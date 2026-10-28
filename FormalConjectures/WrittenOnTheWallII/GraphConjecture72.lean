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
# Written on the Wall II - Conjecture 72

**Verbatim statement (WOWII #72, status O):**
> If G is a simple connected graph, then tree(G) ≥ CEIL[average of ecc(v) + maximum of λ(v) /3]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj72


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture72

open SimpleGraph

/-- The original source assertion, for all finite graph orders at least two.
The parameter n+2 represents every nontrivial finite vertex type up to isomorphism. -/
def conjecture72Statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 2))), G.Connected →
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ⌈averageEccentricity G + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize G : ℝ)

/-- The universal WOWII72 assertion is false. Only the maximum local independence
number is divided by three; the different reading dividing the whole sum is not used.
See Gebendorfer, An unbounded deficit in Written on the Wall II Conjecture72 (2026),
https://github.com/google-deepmind/formal-conjectures/issues/7662. -/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/RhudeJJJJ/formal-conjectures/blob/83fe1c1cd889d6b0635d8ca56e87072db2644bda/Proofs/WOWII72/Full.lean#L55"]
theorem conjecture72 : ¬ conjecture72Statement := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The average eccentricity is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ averageEccentricity G := by
  unfold averageEccentricity
  positivity

end WrittenOnTheWallII.GraphConjecture72
