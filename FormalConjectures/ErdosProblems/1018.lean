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

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.

[KoPy88] Kostochka, A. and Pyber, L., _Small topological complete subgraphs of "dense" graphs_.
Combinatorica (1988), 83-86.
-/

open SimpleGraph Finset

namespace Erdos1018

/-- A simple graph is planar if it admits a topological embedding into the
plane without edge crossings. -/
opaque IsPlanar {V : Type*} [Fintype V] (_ : SimpleGraph V) : Prop

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

/--
Erdős observed that $C_\varepsilon \to \infty$ as $\varepsilon \to 0$: any function $f$ witnessing
the main statement for all $\varepsilon > 0$ must satisfy $f(\varepsilon) \to \infty$ as
$\varepsilon \to 0^+$.
-/
@[category research solved, AMS 5]
theorem erdos_1018_C_tends_to_infinity :
    ∀ f : ℝ → ℕ, (∀ ε > 0, ∀ᶠ n in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        haveI := dG;
        G.edgeFinset.card ≥ ⌈(n : ℝ) ^ (1 + ε)⌉₊ →
        ∃ S : Finset (Fin n), S.card ≤ f ε ∧
          ¬ IsPlanar (G.induce (↑S : Set (Fin n)))) →
    Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  sorry

end Erdos1018
