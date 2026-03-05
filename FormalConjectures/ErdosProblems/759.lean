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
# Erdős Problem 759

*Reference:* [erdosproblems.com/759](https://www.erdosproblems.com/759)

The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours
needed to colour the vertices of $G$ such that each colour class induces either
a complete graph or an empty graph.

Let $z(S_n)$ be the maximum value of $\zeta(G)$ over all graphs $G$ which can be embedded
on $S_n$, the orientable surface of genus $n$. Determine the growth rate of $z(S_n)$.

A problem of Erdős and Gimbel [ErGi93]. Gimbel [Gi86] proved that
$$\sqrt{n} / \log n \ll z(S_n) \ll \sqrt{n}.$$

Solved by Gimbel and Thomassen [GiTh97], who proved
$$z(S_n) \asymp \sqrt{n} / \log n.$$

[ErGi93] Erdős, P. and Gimbel, J., *Some problems and results in cochromatic theory*, 1993.

[Gi86] Gimbel, J., *Some remarks on the cochromatic number of a graph*, 1986.

[GiTh97] Gimbel, J. and Thomassen, C., *Coloring graphs with fixed genus and girth*, 1997.
-/

open SimpleGraph Real

namespace Erdos759

/-- A colouring $c : V \to \operatorname{Fin}(k)$ is a cochromatic colouring of $G$ if every colour
class induces either a complete subgraph or an independent set. -/
def IsCochromaticColouring {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number $\zeta(G)$ of a finite graph $G$: the minimum number of
colours in a cochromatic colouring. -/
noncomputable def cochromaticNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromaticColouring G k c}

/-- Embeddability of a finite simple graph on the orientable surface of genus $n$.
This is axiomatized since surface topology is not available in Mathlib. -/
opaque IsEmbeddableOnSurface {m : ℕ} (_ : SimpleGraph (Fin m)) (_ : ℕ) : Prop

/-- $z(S_n)$: the maximum cochromatic number over all finite graphs embeddable
on the orientable surface of genus $n$. -/
noncomputable def maxCochromaticOnSurface (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (m : ℕ) (G : SimpleGraph (Fin m)),
    IsEmbeddableOnSurface G n ∧ cochromaticNumber G = k}

/--
Erdős Problem 759, upper bound (Gimbel–Thomassen [GiTh97]):

There exist $C > 0$ and $N_0$ such that for all $n \geq N_0$,
$$z(S_n) \leq C \cdot \sqrt{n} / \log n.$$
-/
@[category research solved, AMS 5]
theorem erdos_759 :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxCochromaticOnSurface n : ℝ) ≤
        C * Real.sqrt (n : ℝ) / Real.log (n : ℝ) := by
  sorry

/--
Erdős Problem 759, lower bound (Gimbel [Gi86]):

There exist $C > 0$ and $N_0$ such that for all $n \geq N_0$,
$$z(S_n) \geq C \cdot \sqrt{n} / \log n.$$
-/
@[category research solved, AMS 5]
theorem erdos_759.variants.lower_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxCochromaticOnSurface n : ℝ) ≥
        C * Real.sqrt (n : ℝ) / Real.log (n : ℝ) := by
  sorry

end Erdos759
