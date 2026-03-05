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
# Erdős Problem 797

*Reference:* [erdosproblems.com/797](https://www.erdosproblems.com/797)

Let `f(d)` be the maximal acyclic chromatic number of any graph with maximum degree `d`.
Estimate `f(d)`. In particular, is it true that `f(d) = o(d²)`?

[AlBe76] Albertson, M. O. and Berman, D. M., *Every planar graph has an acyclic
7-coloring*, 1976.

[AMR91] Alon, N., McDiarmid, C., and Reed, B., *Acyclic coloring of graphs*, 1991.
-/

open SimpleGraph Real Classical

namespace Erdos797

/-- A proper coloring of $G$ is acyclic if for every pair of distinct colors,
    the subgraph induced by vertices of those two colors is acyclic (a forest). -/
def IsAcyclicColoring {V : Type*} (G : SimpleGraph V) {α : Type*}
    (c : G.Coloring α) : Prop :=
  ∀ a b : α, a ≠ b →
    (G.induce {v : V | c v = a ∨ c v = b}).IsAcyclic

/--
Let $f(d)$ be the maximal acyclic chromatic number of any graph with maximum
degree $d$. Alon, McDiarmid, and Reed [AMR91] showed
$$d^{4/3} / (\log d)^{1/3} \ll f(d) \ll d^{4/3}.$$
-/
@[category research solved, AMS 5]
theorem erdos_797 :
    -- Upper bound: f(d) ≪ d^{4/3}
    (∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ) (G : SimpleGraph (Fin n)),
        (∀ v, G.degree v ≤ d) →
        ∃ (k : ℕ) (c : G.Coloring (Fin k)),
          IsAcyclicColoring G c ∧ (k : ℝ) ≤ C * (d : ℝ) ^ ((4 : ℝ) / 3)) ∧
    -- Lower bound: f(d) ≫ d^{4/3} / (log d)^{1/3}
    (∃ C : ℝ, 0 < C ∧
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
          (∀ v, G.degree v ≤ d) ∧
          ∀ (k : ℕ), (∃ c : G.Coloring (Fin k), IsAcyclicColoring G c) →
            C * (d : ℝ) ^ ((4 : ℝ) / 3) / (Real.log (d : ℝ)) ^ ((1 : ℝ) / 3) ≤ (k : ℝ)) := by
  sorry

end Erdos797
