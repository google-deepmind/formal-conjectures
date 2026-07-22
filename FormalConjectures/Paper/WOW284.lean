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

import FormalConjecturesUtil

/-!
# Written on the Wall conjecture 284

*References:*
- [Distance Spectra of Graphs: A Survey](https://doi.org/10.1016/j.laa.2014.06.010),
  by *Mustapha Aouchiche and Pierre Hansen*, Linear Algebra and its Applications 458 (2014),
  Conjecture 7.16.
- [Moore Graphs of Diameter Two and the Failure of WOW-284](https://github.com/SamPetkov/wow284),
  by *Samuil Petkov*.

The survey attributes the conjecture to Siemion Fajtlowicz's 1998
*Written on the Wall* report.
-/

namespace WOW284

open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α]

/-- The average degree of the neighbors of a vertex. -/
def dualDegree (G : SimpleGraph α) (v : α) : ℝ :=
  (∑ u ∈ G.neighborFinset v, (G.degree u : ℝ)) / G.degree v

/-- The minimum dual degree of a nonempty finite graph. -/
def minimumDualDegree [Nonempty α] (G : SimpleGraph α) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (dualDegree G)

/-- The real distance matrix of a finite graph. -/
def distanceMatrix (G : SimpleGraph α) : Matrix α α ℝ :=
  fun u v ↦ G.dist u v

/-- The real distance matrix is Hermitian. -/
@[category API, AMS 5]
lemma distanceMatrix_isHermitian (G : SimpleGraph α) : (distanceMatrix G).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro u v
  simp [distanceMatrix, SimpleGraph.dist_comm]

/-- The least eigenvalue of the real distance matrix of a nonempty finite graph. -/
def leastDistanceEigenvalue [DecidableEq α] [Nonempty α] (G : SimpleGraph α) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (distanceMatrix_isHermitian G).eigenvalues

/--
WOW-284 asserted that every connected graph on at least three vertices with girth at least five
has minimum dual degree at most the negative of its least distance eigenvalue. It is false: the
50-vertex Hoffman--Singleton graph is a counterexample.

See Conjecture 7.16 of
[Aouchiche--Hansen](https://doi.org/10.1016/j.laa.2014.06.010).
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/SamPetkov/wow284/tree/08ae20d27792d5f5c2a2587d51b5e2256c1ae06a/lean"]
theorem wow_284 :
    ¬ ∀ (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] (G : SimpleGraph α),
        3 ≤ Fintype.card α → G.Connected → 5 ≤ G.egirth →
          minimumDualDegree G ≤ -leastDistanceEigenvalue G := by
  sorry

end

end WOW284
