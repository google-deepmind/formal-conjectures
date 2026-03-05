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
# Erdős Problem 1018

*Reference:* [erdosproblems.com/1018](https://www.erdosproblems.com/1018)

For every ε > 0, there exists a constant C such that every simple graph on n vertices with at
least ⌈n^{1+ε}⌉ edges contains an induced subgraph on at most C vertices which is non-planar.

[Er71] Erdős, P., 1971.

[KoPy88] Kostochka, A. and Pyber, L., 1988.
-/

open SimpleGraph Finset

namespace Erdos1018

/-- A simple graph is planar if it admits a topological embedding into the
plane without edge crossings. -/
def IsPlanar {V : Type*} (_ : SimpleGraph V) : Prop := sorry

/--
Erdős Problem 1018 [Er71]:

For every $\varepsilon > 0$, there exists a constant $C$ (depending on $\varepsilon$) and a
threshold $N_0$ such that, for all $n \ge N_0$, every simple graph on $n$ vertices with at
least $\lceil n^{1+\varepsilon} \rceil$ edges contains an induced subgraph on at most $C$ vertices
which is non-planar.

Solved by Kostochka and Pyber [KoPy88].
-/
@[category research solved, AMS 5]
theorem erdos_1018 :
    ∀ ε : ℝ, ε > 0 →
      ∃ (C N₀ : ℕ), ∀ n : ℕ, n ≥ N₀ →
        ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
          haveI := dG;
          G.edgeFinset.card ≥ ⌈(n : ℝ) ^ (1 + ε)⌉₊ →
          ∃ S : Finset (Fin n), S.card ≤ C ∧
            ¬ IsPlanar (G.induce (↑S : Set (Fin n))) := by
  sorry

end Erdos1018
