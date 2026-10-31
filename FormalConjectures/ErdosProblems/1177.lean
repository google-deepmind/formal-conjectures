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
module

public import FormalConjecturesUtil
public import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Uniform

/-!
# Erdős Problem 1177

*References:*
- [erdosproblems.com/1177](https://www.erdosproblems.com/1177)
- [Li26] Li, E., *A Resolution of Erdős Problems 593 and 1177: Obligatory Triple Systems
  and Exact Spectra*. [arXiv:2606.24882v2](https://arxiv.org/abs/2606.24882v2) (2026),
  Corollary 1.4.
-/

@[expose] public section

namespace Erdos1177

open Cardinal Filter Asymptotics

/--
Let $G$ be a finite $3$-uniform hypergraph, and let $F_G(\kappa)$ denote the collection of
$3$-uniform hypergraphs with chromatic number $\kappa$ not containing $G$. If
$F_G(\aleph_1)$ is non-empty, then it contains a hypergraph on at most
$2^{2^{\aleph_0}}$ vertices. Li [Li26, Corollary 1.4(1)] proved this.
-/
@[category research solved, AMS 3 5]
theorem erdos_1177.parts.i :
    ∀ (W : Type) [Fintype W] (G : UniformHypergraph W 3),
    G.HasAvoidingChromaticCardinal ℵ₁ →
      ∃ (V : Type) (_ : DecidableEq V) (X : UniformHypergraph V 3),
        X.chromaticCardinal = ℵ₁ ∧ ¬ G.Appears X ∧
          Cardinal.mk V ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ ℵ₀) := by
  sorry

/--
The assertion that two non-empty avoidance families $F_G(\aleph_1)$ and $F_H(\aleph_1)$
always have non-empty intersection is false. Li [Li26, Corollary 1.4(2)] gives a
counterexample using two triples sharing a pair and the loose seven-cycle.
-/
@[category research solved, AMS 3 5]
theorem erdos_1177.parts.ii :
    ¬ ∀ (W U : Type) [Fintype W] [Fintype U]
    (G : UniformHypergraph W 3) (H : UniformHypergraph U 3),
    G.HasAvoidingChromaticCardinal ℵ₁ → H.HasAvoidingChromaticCardinal ℵ₁ →
      ∃ (V : Type) (_ : DecidableEq V) (X : UniformHypergraph V 3),
        X.chromaticCardinal = ℵ₁ ∧ ¬ G.Appears X ∧ ¬ H.Appears X := by
  sorry

/--
If $\kappa,\lambda$ are uncountable cardinals and $F_G(\kappa)$ is non-empty then
$F_G(\lambda)$ is non-empty. Li [Li26, Corollary 1.4(3)] proved this.
-/
@[category research solved, AMS 3 5]
theorem erdos_1177.parts.iii :
    ∀ (W : Type) [Fintype W] (G : UniformHypergraph W 3)
    (κ μ : Cardinal), ℵ₀ < κ → ℵ₀ < μ →
      G.HasAvoidingChromaticCardinal κ → G.HasAvoidingChromaticCardinal μ := by
  sorry

end Erdos1177
