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
# Erdős Problem 760

*Reference:* [erdosproblems.com/760](https://www.erdosproblems.com/760)

The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours
needed to colour the vertices of $G$ such that each colour class induces either
a complete graph or an empty graph.

If $G$ is a graph with chromatic number $\chi(G) = m$ then must $G$ contain a subgraph $H$
with $\zeta(H) \gg m / \log m$?

A problem of Erdős and Gimbel [ErGi93], who proved that there must exist a
subgraph $H$ with $\zeta(H) \gg (m / \log m)^{1/2}$. The proposed bound would be best
possible, as shown by taking $G$ to be a complete graph.

The answer is yes, proved by Alon, Krivelevich, and Sudakov [AKS97].

[ErGi93] Erdős, P. and Gimbel, J.

[AKS97] Alon, N., Krivelevich, M., and Sudakov, B.
-/

open SimpleGraph Real

namespace Erdos760

/-- A colouring $c : V \to \operatorname{Fin} k$ is a cochromatic colouring of $G$ if every
colour class induces either a complete subgraph or an independent set. -/
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

/--
**Erdős Problem 760** (Proved, Alon–Krivelevich–Sudakov [AKS97]):

There exists a constant $C > 0$ such that for every graph $G$ with sufficiently
large chromatic number $m = \chi(G)$, there exists an induced subgraph $H$ of $G$ with
cochromatic number $\zeta(H) \geq C \cdot m / \log m$.
-/
@[category research solved, AMS 5]
theorem erdos_760 :
    answer(True) ↔
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.chromaticNumber.toNat ≥ N₀ →
        ∃ (S : Finset (Fin n)),
          (cochromaticNumber (G.induce (↑S : Set (Fin n))) : ℝ) ≥
            C * (G.chromaticNumber.toNat : ℝ) / Real.log (G.chromaticNumber.toNat : ℝ) := by
  sorry

end Erdos760
