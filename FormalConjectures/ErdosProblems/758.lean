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
# Erdős Problem 758

*Reference:* [erdosproblems.com/758](https://www.erdosproblems.com/758)

The cochromatic number of $G$, denoted $\zeta(G)$, is the minimum number of colours
needed to colour the vertices of $G$ such that each colour class induces either
a complete graph or an empty graph (independent set). Let $z(n)$ be the maximum
value of $\zeta(G)$ over all graphs $G$ with $n$ vertices.

[ErGi93] Erdős, P. and Gimbel, J., *Some problems and results in cochromatic theory* (1993).

[Gi86] Gimbel, J., *The chromatic and cochromatic number of a graph* (1986).
-/

open SimpleGraph

namespace Erdos758

/-- A cochromatic coloring of a simple graph $G$ with $k$ colors is a function
$c : V \to \text{Fin}(k)$ such that each color class is either a clique (all pairs
adjacent) or an independent set (no pairs adjacent). -/
def IsCochromaticColoring {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v : V, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v : V, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number $\zeta(G)$: the minimum number of colors needed for a
cochromatic coloring of $G$. -/
noncomputable def cochromaticNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromaticColoring G k c}

/-- $z(n)$: the maximum cochromatic number over all simple graphs on $n$
vertices. -/
noncomputable def maxCochromaticNumber (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n), cochromaticNumber G = k}

/--
Erdős Problem 758 [ErGi93]:

Is it true that $z(12) = 4$, where $z(n)$ is the maximum cochromatic number
over all graphs on $n$ vertices?

Resolved: $z(12) = 4$ (confirmed computationally by Bhavik Mehta).
-/
@[category research solved, AMS 5]
theorem erdos_758 : answer(True) ↔ maxCochromaticNumber 12 = 4 := by
  sorry

end Erdos758
