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
# Written on the Wall II - Conjecture 309

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [J. J. Gebendorfer, An Infinite Family of Counterexamples to Written on the Wall II,
  Conjecture 309](https://doi.org/10.5281/zenodo.21553295)

The conjecture is false for the clique blow-ups $C_5[K_k]$ for every $k \geq 3$.
-/

namespace WrittenOnTheWallII.GraphConjecture309

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The number of edges whose endpoints are at the same even distance from $v$. -/
def evenHorizontal (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (G.edgeFinset.filter fun e =>
    let distances := e.toFinset.image (G.computable_dist v)
    distances.card = 1 ∧ ∃ d ∈ distances, Even d).card

/-- The maximum of $\operatorname{distEven}(v)-\operatorname{evenHorizontal}(v)$. -/
noncomputable def maxEvenCorrection (G : SimpleGraph V) [Nonempty V]
    [DecidableRel G.Adj] : ℤ :=
  (Finset.univ.image
    (fun v => (G.distEven v : ℤ) - (evenHorizontal G v : ℤ))).max' (by simp)

/-- The minimum complement-edge neighborhood-union order, when a complement edge exists. -/
def minComplementEdgeNeighborhood (G : SimpleGraph V)
    [DecidableRel G.Adj] : Option ℕ :=
  Gᶜ.edgeFinset.image
    (fun e => Sym2.lift ⟨fun u w =>
      (Gᶜ.neighborFinset u ∪ Gᶜ.neighborFinset w).card,
      fun u w => by
        change (Gᶜ.neighborFinset u ∪ Gᶜ.neighborFinset w).card =
          (Gᶜ.neighborFinset w ∪ Gᶜ.neighborFinset u).card
        rw [Finset.union_comm]⟩ e) |>.min

/-- The universal inequality proposed in WOWII Conjecture 309. -/
def Conjecture309Statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
    ∀ mt ∈ minComplementEdgeNeighborhood G,
      (G.totalDominationNumber : ℝ) ≤
        ((maxEvenCorrection G : ℝ) + (mt : ℝ)) / 2

/--
Does every finite simple connected graph $G$ of order greater than two satisfy
$$
\gamma_t(G) \leq \frac{1}{2}\left(
\max_v(\operatorname{distEven}(v)-\operatorname{evenHorizontal}(v))+
\min_{e\in E(\overline G)}|N_{\overline G}(e)|\right)?
$$
Gebendorfer disproved the statement with the family $C_5[K_k]$, $k \geq 3$.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/Kuberwastaken/c5-k4/blob/c9daf0f594d6d5b264c6cd54dc9eec488cb64741/lean/GraphConjecture309.lean"]
theorem conjecture309 : answer(False) ↔ Conjecture309Statement := by
  sorry

end WrittenOnTheWallII.GraphConjecture309
