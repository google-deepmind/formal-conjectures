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
# Erdős Problem 1177

*References:*
- [erdosproblems.com/1177](https://www.erdosproblems.com/1177)
-/

namespace Erdos1177

open Cardinal Filter Asymptotics

/--
Let $G$ be a finite $3$-uniform hypergraph, and let $F_G(\kappa)$ denote the collection of
$3$-uniform hypergraphs with chromatic number $\kappa$ not containing $G$. If $F_G(\aleph_1)$ is not
empty then there exists $X\in F_G(\aleph_1)$ of cardinality at most $2^{2^{\aleph_0}}$. If both
$F_G(\aleph_1)$ and $F_H(\aleph_1)$ are non-empty then $F_G(\aleph_1)\cap F_H(\aleph_1)$ is
non-empty. If $\kappa,\lambda$ are uncountable cardinals and $F_G(\kappa)$ is non-empty then
$F_G(\lambda)$ is non-empty.
-/
@[category research open, AMS 3 5]
theorem erdos_1177.parts.i :
    ∀ (W : Type) [Fintype W] (G : UniformHypergraph W 3),
    G.HasAvoidingChromaticCardinal (by decide) ℵ₁ →
      ∃ (V : Type) (_ : DecidableEq V) (X : UniformHypergraph V 3),
        X.chromaticCardinal (by decide) = ℵ₁ ∧ ¬ G.Appears X ∧
          Cardinal.mk V ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ ℵ₀) := by
  sorry

/--
If both $F_G(\aleph_1)$ and $F_H(\aleph_1)$ are non-empty then
$F_G(\aleph_1)\cap F_H(\aleph_1)$ is non-empty.
-/
@[category research open, AMS 3 5]
theorem erdos_1177.parts.ii :
    ∀ (W U : Type) [Fintype W] [Fintype U]
    (G : UniformHypergraph W 3) (H : UniformHypergraph U 3),
    G.HasAvoidingChromaticCardinal (by decide) ℵ₁ → H.HasAvoidingChromaticCardinal (by decide) ℵ₁ →
      ∃ (V : Type) (_ : DecidableEq V) (X : UniformHypergraph V 3),
        X.chromaticCardinal (by decide) = ℵ₁ ∧ ¬ G.Appears X ∧ ¬ H.Appears X := by
  sorry

/--
If $\kappa,\lambda$ are uncountable cardinals and $F_G(\kappa)$ is non-empty then
$F_G(\lambda)$ is non-empty.
-/
@[category research open, AMS 3 5]
theorem erdos_1177.parts.iii :
    ∀ (W : Type) [Fintype W] (G : UniformHypergraph W 3)
    (κ μ : Cardinal), ℵ₀ < κ → ℵ₀ < μ →
      G.HasAvoidingChromaticCardinal (by decide) κ → G.HasAvoidingChromaticCardinal (by decide) μ := by
  sorry

end Erdos1177
