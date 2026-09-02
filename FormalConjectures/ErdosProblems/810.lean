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
# Erdős Problem 810

*References:*
- [erdosproblems.com/810](https://www.erdosproblems.com/810)
- [BEGS89] Burr, S. A., Erdős, P., Graham, R. L., and Sós, V. T.,
  *Maximal anti-Ramsey graphs and the strong chromatic number*.
  J. Graph Theory 13 (1989), no. 3, 263–282.
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (1991), 397–406.
-/

namespace Erdos810

open Filter

/-- Four objects are pairwise distinct. -/
def PairwiseDistinct4 {α : Type _} (a b c d : α) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- The vertices $a,b,c,d$ form a $C_4$ in cyclic order. -/
def IsC4 {n : ℕ} (G : SimpleGraph (Fin n)) (a b c d : Fin n) : Prop :=
  PairwiseDistinct4 a b c d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- An edge-colouring by $n$ colours such that reversing an edge gives the same colour and every
$C_4$ receives four distinct colours. -/
def C4RainbowColoring {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Fin n → Fin n) : Prop :=
  (∀ a b, G.Adj a b → color a b = color b a) ∧
    ∀ a b c d, IsC4 G a b c d →
      PairwiseDistinct4 (color a b) (color b c) (color c d) (color d a)

/-- Does there exist some $\epsilon>0$ such that, for all sufficiently large $n$, there exists a
graph $G$ on $n$ vertices with at least $\epsilon n^2$ edges whose edges can be coloured with $n$
colours so that every $C_4$ receives four distinct colours? -/
@[category research open, AMS 5]
theorem erdos_810 : answer(sorry) ↔ ∃ ε > 0, ∀ᶠ n in atTop,
    ∃ G : SimpleGraph (Fin n), ∃ color : Fin n → Fin n → Fin n,
      ε * (n : ℝ) ^ 2 ≤ (G.edgeSet.ncard : ℝ) ∧ C4RainbowColoring G color := by
  sorry

end Erdos810
