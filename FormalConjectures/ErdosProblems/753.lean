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
# Erdős Problem 753

*Reference:* [erdosproblems.com/753](https://www.erdosproblems.com/753)

Does there exist some constant $c > 0$ such that
$\chi_L(G) + \chi_L(G^c) > n^{1/2+c}$ for every graph $G$ on $n$ vertices?
Disproved by Alon [Al92], who showed that the sum can be bounded above by
$C \sqrt{n \log n}$ for some absolute constant $C > 0$.

[ERT80] Erdős, P., Rubin, A. L., and Taylor, H., _Choosability in graphs_. Proceedings of the
West Coast Conference on Combinatorics, Graph Theory and Computing (1980), 125-157.

[Al92] Alon, N., _Choice numbers of graphs: a probabilistic approach_. Combinatorics, Probability
and Computing 1 (1992), 107-114.
-/

open SimpleGraph

namespace Erdos753

/-- A graph $G$ is $k$-choosable ($k$-list-colorable) if for every assignment of lists
of size at least $k$ to the vertices, there exists a proper coloring where each
vertex receives a color from its list. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (L : V → Finset ℕ), (∀ v, k ≤ (L v).card) →
    ∃ f : V → ℕ, (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v)

/-- The list chromatic number (choice number) of a graph: the minimum $k$ such
that $G$ is $k$-choosable. -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsChoosable G k}

/--
**Erdős Problem 753** [ERT80]:

Does there exist some constant $c > 0$ such that
$\chi_L(G) + \chi_L(G^c) > n^{1/2+c}$ for every graph $G$ on $n$ vertices?
Disproved by Alon [Al92].
-/
@[category research solved, AMS 5]
theorem erdos_753 :
    answer(False) ↔
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        ∀ (G : SimpleGraph (Fin n)),
          (listChromaticNumber G + listChromaticNumber Gᶜ : ℝ) >
            (n : ℝ) ^ (1 / 2 + c) := by
  sorry

/--
**Alon's upper bound** [Al92]:

There exists an absolute constant $C > 0$ such that for every $n \geq 2$, there exists
a graph $G$ on $n$ vertices with
$\chi_L(G) + \chi_L(G^c) \leq C \cdot \sqrt{n \cdot \log n}$.
-/
@[category research solved, AMS 5]
theorem erdos_753.variants.alon_upper_bound :
    ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      ∃ (G : SimpleGraph (Fin n)),
        (listChromaticNumber G + listChromaticNumber Gᶜ : ℝ) ≤
          C * Real.sqrt (n * Real.log n) := by
  sorry

end Erdos753
