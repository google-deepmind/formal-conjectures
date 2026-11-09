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
# Written on the Wall II - Conjecture 32

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture32

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

set_option linter.style.formal_proof_palomar false in
/--
WOWII [Conjecture 32](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\operatorname{path}(G) \ge \operatorname{dist}\_{\operatorname{avg}}(A) + 0.5 \cdot \operatorname{ecc}\_{\operatorname{avg}}(M)$,
where $\operatorname{path}(G)$ is the number of vertices of a largest induced path of $G$,
$A$ is the set of minimum-degree vertices, $M$ is the set of maximum-degree vertices,
$\operatorname{dist}\_{\operatorname{avg}}(A)$ is the average of all nonzero distances
$\operatorname{dist}\_G(u, v)$ with $u, v \in A$ (i.e. the average over ordered pairs of
distinct vertices of $A$; it is taken to be $0$ when $A$ has fewer than two vertices), and
$\operatorname{ecc}\_{\operatorname{avg}}(M)$ is the average eccentricity of the vertices
in $M$.

The conjecture is false, the authors present a counterexample: "The path on 5 vertices
is a counterexample, path = 5, distavg(A) = 4 and the average of eccentricity of maximum
degree vertices is 8/3."

Independent Lean formalization by Wentao Li, with AI assistance. An earlier Lean proof
is recorded in the Epoch review archived in
[tadamcz/fc-review-results](https://github.com/tadamcz/fc-review-results/blob/971290dd3e0e4dce063f98feaa8ecb9e51acd5ec/data/782312817c/files/WrittenOnTheWallII/GraphConjecture32.json).
-/
@[category research solved, question, AMS 5,
  formal_proof using lean4 at "https://github.com/VictorLiwentao/lean-graph-proofs/blob/b60c2e548910b32eb3b602f6a8e67af806e4b9f6/LeanGraphProofs/WOWII32.lean#L114"]
theorem conjecture32 :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      let A : Finset α := Finset.univ.filter (fun v => G.degree v = G.minDegree)
      let M : Finset α := Finset.univ.filter (fun v => G.degree v = G.maxDegree)
      let distavgA : ℝ := (∑ p ∈ A.offDiag, (G.dist p.1 p.2 : ℝ)) / (A.offDiag.card : ℝ)
      let eccavg (S : Finset α) : ℝ := (∑ v ∈ S, (G.eccent v).toNat) / (S.card : ℝ)
      distavgA + (1 / 2 : ℝ) * eccavg M ≤ (path G : ℝ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant cast to ℝ is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℝ) := Nat.cast_nonneg _

/-- In `K₃`, the max degree is 2. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 3)).maxDegree = 2 := by decide

end WrittenOnTheWallII.GraphConjecture32
