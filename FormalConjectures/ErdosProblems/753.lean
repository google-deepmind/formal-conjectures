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
# Erdős Problem 753

*References:*
- [erdosproblems.com/753](https://www.erdosproblems.com/753)
- [Al92] Alon, Noga, *Choice numbers of graphs: a probabilistic approach*. Combin. Probab.
  Comput. (1992), 107-114.
-/

namespace Erdos753

/--
A graph $G$ is $k$-choosable if for any assignment of a list of $k$ colours to each vertex of $G$
(perhaps different lists for different vertices) a colouring of each vertex by a colour on its list
can be chosen such that adjacent vertices receive distinct colours.
-/
def IsKChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) → ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v

/--
The list chromatic number $\chi_L(G)$, defined to be the minimal $k$ such that $G$ is
$k$-choosable.
-/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKChoosable G k}

/--
The list chromatic number $\chi_L(G)$ is defined to be the minimal $k$ such that for any
assignment of a list of $k$ colours to each vertex of $G$ (perhaps different lists for different
vertices) a colouring of each vertex by a colour on its list can be chosen such that adjacent
vertices receive distinct colours.

Does there exist some constant $c>0$ such that
\[\chi_L(G)+\chi_L(G^c)> n^{1/2+c}\]
for every graph $G$ on $n$ vertices (where $G^c$ is the complement of $G$)?

A problem of Erdős, Rubin, and Taylor.

The answer is no: Alon [Al92] proved that, for every $n$, there exists a graph $G$ on $n$ vertices
such that
\[\chi_L(G)+\chi_L(G^c)\ll (n\log n)^{1/2},\]
where the implied constant is absolute.
-/
@[category research solved, AMS 5]
theorem erdos_753 : answer(False) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ ((1 : ℝ) / 2 + c) <
        (listChromaticNumber G : ℝ) + (listChromaticNumber Gᶜ : ℝ) := by
  sorry

/--
Alon [Al92] proved that, for every $n$, there exists a graph $G$ on $n$ vertices such that
\[\chi_L(G)+\chi_L(G^c)\ll (n\log n)^{1/2},\]
where the implied constant is absolute.
-/
@[category research solved, AMS 5]
theorem erdos_753.variants.alon :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∃ G : SimpleGraph (Fin n),
      (listChromaticNumber G : ℝ) + (listChromaticNumber Gᶜ : ℝ) ≤
        C * ((n : ℝ) * Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos753
