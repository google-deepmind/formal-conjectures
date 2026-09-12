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
# The linear arboricity conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Linear_arboricity)
* [AEH81] Akiyama, J., Exoo, G., and Harary, F. (1981). "Covering and packing in graphs. IV.
  Linear arboricity." *Networks* 11, pp. 69--72.
* [EP84] Enomoto, H. and Péroche, B. (1984). "The linear arboricity of some regular graphs."
  *J. Graph Theory* 8, pp. 309--324.
* [Al88] Alon, N. (1988). "The linear arboricity of graphs." *Israel J. Math.* 62,
  pp. 311--325.
-/

namespace LinearArboricityConjecture

variable {V : Type*}

/-- A **linear forest** is a graph whose connected components are paths: an acyclic graph in
which every vertex has at most two neighbours. -/
def IsLinearForest (F : SimpleGraph V) : Prop :=
  F.IsAcyclic ∧ ∀ v, (F.neighborSet v).ncard ≤ 2

/-- `G` decomposes into `k` linear forests: there are `k` linear forests such that every edge
of `G` lies in exactly one of them. -/
def HasLinearForestDecomposition (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : Fin k → SimpleGraph V, (∀ i, IsLinearForest (D i)) ∧
    ∀ u v, G.Adj u v ↔ ∃! i, (D i).Adj u v

/-- The **linear arboricity** `la(G)`: the least number of linear forests into which the edges
of `G` can be partitioned. -/
noncomputable def linearArboricity (G : SimpleGraph V) : ℕ :=
  sInf {k | HasLinearForestDecomposition G k}

/-- The empty graph is a linear forest. -/
@[category API, AMS 5]
lemma isLinearForest_bot : IsLinearForest (⊥ : SimpleGraph V) := by
  constructor
  · intro v c hc
    cases c with
    | nil => exact hc.ne_nil rfl
    | cons h p => exact h
  · intro v
    have h : (⊥ : SimpleGraph V).neighborSet v = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun w hw => hw
    rw [h]
    simp

/--
**The linear arboricity conjecture** (Akiyama–Exoo–Harary [AEH81]).

The edges of every graph of maximum degree `Δ` can be partitioned into at most `⌈(Δ + 1) / 2⌉`
linear forests.
-/
@[category research open, AMS 5]
theorem linear_arboricity_conjecture {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    linearArboricity G ≤ (G.maxDegree + 2) / 2 := by
  sorry

/--
**The linear arboricity conjecture for regular graphs.**

Every `Δ`-regular graph has linear arboricity exactly `⌈(Δ + 1) / 2⌉`. Since a `Δ`-regular
graph is easily seen to have linear arboricity strictly greater than `Δ / 2`, this form of
the conjecture is equivalent to the general upper bound; see [AEH81].
-/
@[category research open, AMS 5]
theorem linear_arboricity_conjecture.variants.regular {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hreg : ∀ v, G.degree v = Δ) :
    linearArboricity G = (Δ + 2) / 2 := by
  sorry

/--
**Cubic graphs have linear arboricity two** (Akiyama–Exoo–Harary [AEH81]).

The edges of every `3`-regular graph can be partitioned into two linear forests, and one
linear forest is not enough.
-/
@[category research solved, AMS 5]
theorem linear_arboricity_conjecture.variants.cubic {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hreg : ∀ v, G.degree v = 3) :
    linearArboricity G = 2 := by
  sorry

/--
**Alon (1988): the linear arboricity conjecture holds asymptotically.**

For every `ε > 0` there is a `Δ₀` such that every graph of maximum degree `Δ ≥ Δ₀` has linear
arboricity at most `(1 / 2 + ε) Δ`.

*Reference:* [Al88].
-/
@[category research solved, AMS 5]
theorem linear_arboricity_conjecture.variants.alon (ε : ℝ) (hε : 0 < ε) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ := by
  sorry

/--
**The empty graph has linear arboricity zero.**

The empty partition witnesses `la(⊥) = 0`.
-/
@[category test, AMS 5]
theorem linear_arboricity_conjecture.variants.bot :
    linearArboricity (⊥ : SimpleGraph V) = 0 := by
  have h : HasLinearForestDecomposition (⊥ : SimpleGraph V) 0 :=
    ⟨fun i => i.elim0, fun i => i.elim0,
      fun u v => iff_of_false (fun h => h) fun ⟨i, _⟩ => i.elim0⟩
  exact Nat.le_zero.mp (Nat.sInf_le h)

end LinearArboricityConjecture
