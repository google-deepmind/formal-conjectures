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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 993

*Reference:* [erdosproblems.com/993](https://www.erdosproblems.com/993)

A question of Alavi, Malde, Schwenk, and Erdős [AMSE87], who showed that the independent set
sequence is not constrained for general graphs (in fact every possible pattern of inequalities
is achieved by some graph).

[AMSE87] Alavi, Y., Malde, P. J., Schwenk, A. J., and Erdős, P., *The vertex independence
sequence of a graph is not constrained*. Congressus Numerantium (1987), 58, 15-23.
-/

open SimpleGraph

namespace Erdos993

/-- The number of independent sets of size $k$ in a simple graph $G$.
An independent set is a set of vertices that are pairwise non-adjacent. -/
def numIndepSets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.powerset.filter (fun s : Finset V =>
    s.card = k ∧ ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → ¬G.Adj u v)).card

/--
Erdős Problem 993 [AMSE87]:

The independent set sequence of any tree or forest is unimodal. That is, if
$i_k(T)$ counts the number of independent sets of vertices of size $k$ in a
forest $T$, then there exists $m \geq 0$ such that
$$
i_0(T) \leq i_1(T) \leq \cdots \leq i_m(T) \geq i_{m+1}(T) \geq i_{m+2}(T) \geq \cdots
$$
-/
@[category research open, AMS 5]
theorem erdos_993 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsAcyclic) :
    ∃ m : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ m → numIndepSets T i ≤ numIndepSets T j) ∧
             (∀ i j : ℕ, m ≤ i → i ≤ j → numIndepSets T j ≤ numIndepSets T i) := by
  sorry

end Erdos993
