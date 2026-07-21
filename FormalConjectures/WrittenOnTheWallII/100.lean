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
# Written on the Wall II - Conjecture 100

**Verbatim statement (WOWII #100, status O):**
> If G is a simple connected graph, then α(G) ≤ CEIL[(maximum of λ(v) + 0.5*length(Ḡ))/2]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100

The WOWII HTML uses `length(Ḡ)` (the bar denotes graph complement); the
extracted JSON in our private repo previously dropped the overline. The
formal statement below uses the Euclidean norm of the degree sequence of `Gᶜ`.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definition of graph length

The WOWII definitions popup defines `length(H)` as the square root of the sum
of the squares of the vertex degrees. This is `degreeL2Norm H` in Lean.
Combined with the overline above, the inequality reads:
  `α(G) ≤ ⌈(max_v l(v) + 0.5 · degreeL2Norm(Gᶜ)) / 2⌉`
where `l(v) = indepNeighbors G v`.
-/

namespace WrittenOnTheWallII.GraphConjecture100

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 100](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100)
(status O):

For a simple connected graph `G`,
`α(G) ≤ ⌈(max_v l(v) + 0.5 · degreeL2Norm(Gᶜ)) / 2⌉`
where `α(G) = G.indepNum` is the independence number,
`max_v l(v)` is the maximum over all vertices of the independence number of
the neighbourhood (in `G`), and `degreeL2Norm(Gᶜ)` is the square root of the
sum of the squares of the degrees in the complement `Gᶜ`.

**Proof outline.** Let `S` be a maximum independent set, let `A = |S|`, let
`T = V(G) \ S`, and let `L` be the maximum local independence number. By
connectedness, every vertex of `S` has a neighbour in `T`, while each vertex
of `T` has at most `L` neighbours in `S`; hence `A ≤ |T|L`. In the complement,
every vertex of `T` has at least `A - L` neighbours in `S`. Double-counting
these complement edges and summing squared complement degrees over `S` and
`T` yields the required lower bound for `degreeL2Norm Gᶜ`. The case `A = 1`
is handled separately, and the remaining arithmetic gives the ceiling bound.

**Provenance.** Solved by Dominic Dabish.

ProofOrchestrator, using OpenAI GPT-5.6 Thinking, assisted with the mathematical
argument and Lean formalization; all formal claims were checked by the pinned
Lean compiler.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/DomTheDeveloper/formal-conjectures/blob/f074b9caff80b611476c74d9e507b19b75d51648/FormalConjectures/WrittenOnTheWallII/100.lean"]
theorem conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  sorry

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

/-- The Euclidean norm of the degree sequence is nonnegative. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 2)) : 0 ≤ degreeL2Norm G := Real.sqrt_nonneg _

end WrittenOnTheWallII.GraphConjecture100
