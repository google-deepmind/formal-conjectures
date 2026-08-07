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
# Erdős Problem 810

*Reference:* [erdosproblems.com/810](https://www.erdosproblems.com/810)

Does there exist `ε > 0` such that, for all sufficiently large `n`, there is a
graph on `n` vertices with at least `ε n^2` edges whose edges can be coloured
with `n` colours so that every `C₄` receives four distinct colours?
-/

noncomputable section

namespace Erdos810

open Classical Filter

/-- A simple graph on the finite vertex type `Fin n`. -/
structure SimpleGraphOn (n : ℕ) where
  Adj : Fin n → Fin n → Prop
  symm : ∀ {u v : Fin n}, Adj u v → Adj v u
  loopless : ∀ v : Fin n, ¬ Adj v v

/-- Four objects are pairwise distinct. -/
def PairwiseDistinct4 {α : Type _} (a b c d : α) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- The unordered edges of a graph, represented by ordered pairs `u < v`. -/
def edgePairs {n : ℕ} (G : SimpleGraphOn n) : Finset (Fin n × Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n × Fin n)).filter fun uv =>
    uv.1 < uv.2 ∧ G.Adj uv.1 uv.2

/-- The vertices `a,b,c,d` form a `C₄` in cyclic order. -/
def IsC4 {n : ℕ} (G : SimpleGraphOn n) (a b c d : Fin n) : Prop :=
  PairwiseDistinct4 a b c d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/--
An edge-colouring by `n` colours such that reversing an edge gives the same
colour and every `C₄` receives four distinct colours.
-/
def C4RainbowColoring {n : ℕ} (G : SimpleGraphOn n)
    (color : Fin n → Fin n → Fin n) : Prop :=
  (∀ a b : Fin n, G.Adj a b → color a b = color b a) ∧
    ∀ a b c d : Fin n,
      IsC4 G a b c d →
        PairwiseDistinct4 (color a b) (color b c) (color c d) (color d a)

/-- The conjectured dense `C₄`-rainbow-colourable graph exists. -/
def Erdos810Conjecture : Prop :=
  ∃ ε : ℝ,
    0 < ε ∧
      ∀ᶠ n in atTop,
        ∃ G : SimpleGraphOn n,
          ∃ color : Fin n → Fin n → Fin n,
            ε * (n : ℝ) ^ 2 ≤ ((edgePairs G).card : ℝ) ∧
              C4RainbowColoring G color

/--
Does there exist `ε > 0` such that for all sufficiently large `n` there is an
`n`-vertex graph with at least `ε n²` edges and an `n`-colour edge-colouring in
which every `C₄` is rainbow?
-/
@[category research open, AMS 5]
theorem erdos_810 : answer(sorry) ↔ Erdos810Conjecture := by
  sorry

end Erdos810

end

