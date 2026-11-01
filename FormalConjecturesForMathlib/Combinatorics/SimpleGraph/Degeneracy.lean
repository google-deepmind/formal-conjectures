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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Graph degeneracy

A graph is $r$-degenerate if each nonempty finite vertex set contains a vertex with at most
$r$ neighbours in that set.
-/

namespace SimpleGraph

open scoped Classical in
/-- The neighbours of `v` lying inside `s`. -/
noncomputable def neighborsWithin {V : Type*} (H : SimpleGraph V) (s : Finset V) (v : V) :
    Finset V := s.filter (H.Adj v)

/-- `H` is `r`-degenerate when every induced subgraph has a vertex of degree at most `r`, that is,
every nonempty vertex set contains a vertex with at most `r` neighbours inside it. -/
def IsDegenerate {V : Type*} (H : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (neighborsWithin H s v).card ≤ r

@[simp]
lemma neighborsWithin_empty {V : Type*} (H : SimpleGraph V) (v : V) :
    H.neighborsWithin ∅ v = ∅ := by
  simp [neighborsWithin]

@[simp]
lemma isDegenerate_bot {V : Type*} (r : ℕ) : (⊥ : SimpleGraph V).IsDegenerate r := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  exact ⟨v, hv, by simp [neighborsWithin]⟩

end SimpleGraph
