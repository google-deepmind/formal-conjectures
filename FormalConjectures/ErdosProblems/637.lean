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
# Erdős Problem 637

*References:*
- [erdosproblems.com/637](https://www.erdosproblems.com/637)
- [Er97d] Erdős, Paul, _Some recent problems and results in graph theory_. Discrete Math. (1997),
  81-85.
- [BuSu07] Bukh, Boris and Sudakov, Benny, _Induced subgraphs of Ramsey graphs with many distinct
  degrees_. J. Combin. Theory Ser. B (2007), 612-619.
- [JKLY20] Jenssen, Matthew and Keevash, Peter and Long, Eoin and Yepremyan, Liana, _Distinct
  degrees in induced subgraphs_. Proc. Amer. Math. Soc. (2020), 3835-3846.
-/

@[expose] public section

open Filter Real SimpleGraph

namespace Erdos637

open scoped Classical in
/-- The number of distinct degrees in the subgraph of `G` induced on `W`. -/
noncomputable def distinctDegrees {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) : ℕ :=
  (W.image fun v ↦ (W.filter (G.Adj v)).card).card

/-- `G` contains no clique or independent set on `C log n` vertices. -/
def IsRamseyGraph {n : ℕ} (C : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
    (S.card : ℝ) < C * log n

/--
If $G$ is a graph on $n$ vertices which contains no complete graph or independent set on
$\gg \log n$ vertices then $G$ contains an induced subgraph on $\gg n$ vertices which contains
$\gg n^{1/2}$ distinct degrees.

A problem of Erdős, Faudree, and Sós. This was proved by Bukh and Sudakov [BuSu07].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos637.lean#L1062"]
theorem erdos_637 : answer(True) ↔
    ∀ C : ℝ, 0 < C → ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), IsRamseyGraph C G →
        ∃ W : Finset (Fin n), α * n ≤ W.card ∧ β * √n ≤ distinctDegrees G W := by
  sorry

/-- Jenssen, Keevash, Long, and Yepremyan [JKLY20] have proved that there must exist an induced
subgraph which contains $\gg n^{2/3}$ distinct degrees (with no restriction on the number of
vertices). -/
@[category research solved, AMS 5]
theorem erdos_637.variants.jenssen_keevash_long_yepremyan :
    ∀ C : ℝ, 0 < C → ∃ β : ℝ, 0 < β ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), IsRamseyGraph C G →
        ∃ W : Finset (Fin n), β * (n : ℝ) ^ (2 / 3 : ℝ) ≤ distinctDegrees G W := by
  sorry

end Erdos637
