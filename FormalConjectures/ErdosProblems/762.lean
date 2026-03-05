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
# Erdős Problem 762

*Reference:* [erdosproblems.com/762](https://www.erdosproblems.com/762)

The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours
needed to colour the vertices of $G$ such that each colour class induces either a
complete graph or empty graph.

A conjecture of Erdős, Gimbel, and Straight [EGS90], who proved that for every
$n > 2$ there exists some $f(n)$ such that if $G$ contains no clique on $n$ vertices
then $\chi(G) \leq \zeta(G) + f(n)$.

This has been disproved by Steiner [St24b], who constructed a graph $G$ with
$\omega(G) = 4$, $\zeta(G) = 4$, and $\chi(G) = 7$.

[EGS90] Erdős, P., Gimbel, J., and Straight, H.J., _Chromatic number versus cochromatic
number in graphs with bounded clique number_, European J. Combin. 11 (1990), 235–240.

[St24b] Steiner, R., _A counterexample to the Erdős–Gimbel–Straight conjecture_, 2024.
-/

open SimpleGraph

namespace Erdos762

/-- A cochromatic colouring: each colour class induces either a complete
    subgraph or an independent set. -/
def IsCochromaticColouring {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number $\zeta(G)$: minimum number of colours in a cochromatic
    colouring. -/
noncomputable def cochromaticNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromaticColouring G k c}

/--
**Erdős Problem 762** (disproved, Steiner [St24b]):

Is it true that if $G$ has no $K_5$ and $\zeta(G) \geq 4$ then
$\chi(G) \leq \zeta(G) + 2$?

Steiner constructed a counterexample: a graph $G$ with $\omega(G) = 4$,
$\zeta(G) = 4$, and $\chi(G) = 7 > \zeta(G) + 2 = 6$.
-/
@[category research solved, AMS 5]
theorem erdos_762 :
    answer(False) ↔
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        G.CliqueFree 5 →
          cochromaticNumber G ≥ 4 →
            G.chromaticNumber ≤ cochromaticNumber G + 2 := by
  sorry

end Erdos762
