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

import FormalConjectures.Util.ProblemImports

namespace Arxiv.«2107.00295»

/-!
# Conjecture 1.6

*Reference:* [arxiv/2107.00295](https://arxiv.org/abs/2107.00295)
**On independent domination of regular graphs**
by *Eun-Kyung Cho, Ilkyoo Choi, Boram Park*
-/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A set `S` is a dominating set of a graph `G` if every vertex not in `S`
is adjacent to at least one vertex in `S`. -/
def IsDominatingSet (S : Finset V) : Prop := ∀ v ∉ S, ∃ u ∈ S, G.Adj v u

/-- The independent domination number `i(G)` is the minimum cardinality of
a set that is both independent and dominating. -/
noncomputable def independentDominationNumber : ℕ :=
  ⨅ (S : Finset V) (_ : G.IsIndepSet S ∧ IsDominatingSet G S), S.card

variable (D := G.maxDegree) (i := independentDominationNumber G) (n := Fintype.card V)

/--
**Conjecture 1.6 (Even case).**
For an isolate-free graph `G` on `n` vertices with maximum degree `Δ ≥ 1`,
if `Δ` is even, then `(Δ + 2)² · i(G) ≤ (Δ² + 4) · n`.
-/
@[category research open, AMS 5]
theorem independentDominationEven (hIso : 0 < G.minDegree) (hMax : 1 ≤ D) (hEven : Even D) :
    (D + 2)^2 * i ≤ (D^2 + 4) * n := by
  sorry

/--
**Conjecture 1.6 (Odd case).**
For an isolate-free graph `G` on `n` vertices with maximum degree `Δ ≥ 1`,
if `Δ` is odd, then `(Δ + 1)(Δ + 3) · i(G) ≤ (Δ² + 3) · n`.
-/
@[category research open, AMS 5]
theorem independentDominationOdd (hIso : 0 < G.minDegree) (hMax : 1 ≤ D) (hOdd : Odd D) :
    (D + 1) * (D + 3) * i ≤ (D^2 + 3) * n := by
  sorry

end Arxiv.«2107.00295»
