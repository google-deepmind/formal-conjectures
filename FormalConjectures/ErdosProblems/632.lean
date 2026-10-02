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
# Erdős Problem 632

*References:*
- [erdosproblems.com/632](https://www.erdosproblems.com/632)
- [ERT80] Erdős, Paul and Rubin, Arthur L. and Taylor, Herbert, _Choosability in graphs_. (1980),
  125-157.
- [DHS19] Dvořák, Zdeněk and Hu, Xiaolan and Sereni, Jean-Sébastien, _A 4-choosable graph that
  is not (8:2)-choosable_. Adv. Comb. (2019), Paper No. 5, 9.
-/

@[expose] public section

namespace Erdos632

/-- A graph is $(a,b)$-choosable if for any assignment of a list of $a$ colours to each of its
vertices there is a subset of $b$ colours from each list such that the subsets of adjacent
vertices are disjoint. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = a) →
    ∃ φ : V → Finset ℕ, (∀ v, φ v ⊆ L v ∧ (φ v).card = b) ∧
      ∀ u v, G.Adj u v → Disjoint (φ u) (φ v)

/--
A graph is $(a,b)$-choosable if for any assignment of a list of $a$ colours to each of its
vertices there is a subset of $b$ colours from each list such that the subsets of adjacent
vertices are disjoint.

If $G$ is $(a,b)$-choosable then $G$ is $(am,bm)$-choosable for every integer $m\geq 1$.

A problem of Erdős, Rubin, and Taylor [ERT80]. This is false: Dvořák, Hu, and Sereni [DHS19]
construct a graph which is $(4,1)$-choosable but not $(8,2)$-choosable.
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos632.lean#L66"]
theorem erdos_632 : answer(False) ↔
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (a b m : ℕ),
      1 ≤ b → b ≤ a → 1 ≤ m → IsChoosable G a b → IsChoosable G (a * m) (b * m) := by
  sorry

/-- Dvořák, Hu, and Sereni [DHS19] construct a graph which is $(4,1)$-choosable but not
$(8,2)$-choosable. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos632.lean#L66"]
theorem erdos_632.variants.dvorak_hu_sereni :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      IsChoosable G 4 1 ∧ ¬ IsChoosable G 8 2 := by
  sorry

end Erdos632
