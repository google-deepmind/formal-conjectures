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

public import FormalConjecturesUtil

/-!
# Kazemi's Conjecture 6.1 on total dominator colorings of hypercubes

*References:*
- [A. P. Kazemi, Total Dominator Coloring of the Hypercube Q_(2^n), Conjecture 6.1, p. 10](https://shahindp.com/Contrib_Math/v13/CM26_v13_pp1-10.pdf)
- [J. J. Gebendorfer, Total dominator colorings of hypercubes of dimension 2^n+1, 14 October 2026](https://github.com/google-deepmind/formal-conjectures/issues/7336)

This is Conjecture 6.1, not the separate Question 6.1 in the same source.
The dimension is $2^n+1$. A total dominator coloring is proper, has nonempty
color classes, and every vertex is adjacent to every vertex of some color class.
-/

@[expose] public section
namespace Kazemi.Hypercube
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A proper coloring with nonempty classes in which every vertex totally
dominates some entire color class. Surjectivity excludes vacuous empty classes.
-/
def HasTotalDominatorColoring (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : G.Coloring (Fin k), Function.Surjective c ∧
    ∀ v, ∃ i : Fin k, ∀ w, c w = i → G.Adj v w

noncomputable def totalDominatorChromaticNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | HasTotalDominatorColoring G k}

/-- For every natural $n\ge2$, the total dominator chromatic number of the
hypercube of dimension $2^n+1$ is $2^{2^n-n+1}+2$.
-/
@[category research solved, AMS 5]
theorem conjecture6_1 (n : ℕ) (hn : 2 ≤ n) :
    totalDominatorChromaticNumber (SimpleGraph.hypercube (2^n+1)) = 2^(2^n-n+1)+2 := by
  sorry

end Kazemi.Hypercube
