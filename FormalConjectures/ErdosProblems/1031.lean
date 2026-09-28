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
# Erdős Problem 1031

*References:*
- [erdosproblems.com/1031](https://www.erdosproblems.com/1031)
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [PrRo99] Prömel, Hans Jürgen and Rödl, Vojtěch, *Non-Ramsey graphs are $c\log n$-universal*.
  J. Combin. Theory Ser. A (1999), 379-384.
-/

@[expose] public section

open Filter SimpleGraph
open scoped SimpleGraph

namespace Erdos1031

open scoped Classical in
/--
`G` contains a non-trivial (neither empty nor complete) regular induced subgraph on at least
`L` vertices.
-/
def HasLargeNontrivialRegularInduced {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℝ) : Prop :=
  ∃ (S : Finset V) (d : ℕ), L ≤ S.card ∧ 0 < d ∧ d + 1 < S.card ∧ (G.induce S).IsRegularOfDegree d

/--
If $G$ is a graph on $n$ vertices which contains no trivial (empty or complete) subgraph on
$\geq 10\log n$ many vertices, then must $G$ contain an induced non-trivial regular subgraph on
$\gg \log n$ many vertices?

A question of Erdős, Fajtlowicz, and Staton. Erdős [Er93] writes 'Perhaps very much more is true
but we could not even prove this seemingly weak result'.

By Ramsey's theorem every graph on $n$ vertices contains a trivial subgraph on $\gg \log n$ many
vertices.

This is true, and was proved by Prömel and Rödl [PrRo99], in the strong sense that, for any
$c>0$, if $G$ contains no trivial subgraph on $\geq c\log n$ vertices then $G$ contains all
graphs with $O_c(\log n)$ many vertices as induced subgraphs.

See also [82](https://www.erdosproblems.com/82) for how large an induced regular subgraph a
general graph must contain.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1031.lean#L1776"]
theorem erdos_1031 : answer(True) ↔ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
    (G.cliqueNum : ℝ) < 10 * Real.log n → (G.indepNum : ℝ) < 10 * Real.log n →
      HasLargeNontrivialRegularInduced G (c * Real.log n) := by
  sorry

/--
Prömel and Rödl [PrRo99] proved that, for any $c>0$, if $G$ contains no trivial subgraph on
$\geq c\log n$ vertices then $G$ contains all graphs with $O_c(\log n)$ many vertices as induced
subgraphs.
-/
@[category research solved, AMS 5]
theorem erdos_1031.variants.promel_rodl : ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < c * Real.log n → (G.indepNum : ℝ) < c * Real.log n →
        ∀ k : ℕ, k ≤ C * Real.log n → ∀ H : SimpleGraph (Fin k), H ⊴ G := by
  sorry

/-- By Ramsey's theorem every graph on $n$ vertices contains a trivial subgraph on $\gg \log n$
many vertices. -/
@[category research solved, AMS 5]
theorem erdos_1031.variants.ramsey : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    ∀ G : SimpleGraph (Fin n), c * Real.log n ≤ max G.cliqueNum G.indepNum := by
  sorry

end Erdos1031
