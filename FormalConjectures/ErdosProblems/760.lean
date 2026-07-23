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
# Erdős Problem 760

*References:*
- [erdosproblems.com/760](https://www.erdosproblems.com/760)
- [AKS97] Alon, Noga and Krivelevich, Michael and Sudakov, Benny, *Subgraphs with a large
  cochromatic number*. J. Graph Theory (1997), 295-297.
-/

namespace Erdos760

/--
The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed to
colour the vertices of $G$ such that each colour class induces either a complete graph or
independent set.

If $G$ is a graph with chromatic number $\chi(G)=m$ then must $G$ contain a subgraph $H$ with
\[
\zeta(H) \gg \frac{m}{\log m}?
\]

A problem of Erdős and Gimbel, who proved that there must exist a subgraph $H$ with
\[
\zeta(H) \gg \left(\frac{m}{\log m}\right)^{1/2}.
\]
The proposed bound would be best possible, as shown by taking $G$ to be a complete graph.

The answer is yes, proved by Alon, Krivelevich, and Sudakov.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos760.lean"]
theorem erdos_760 : answer(True) ↔
    ∃ c > (0 : ℝ), ∀ (V : Type*) [Finite V] (G : SimpleGraph V) (m : ℕ),
      G.chromaticNumber = (m : ℕ∞) →
        ∃ H : G.Subgraph, ∃ k : ℕ, ((k : ℕ∞) ≤ H.coe.cochromaticNumber) ∧
          (c * (m : ℝ) / Real.log (m : ℝ) ≤ (k : ℝ)) := by
  sorry

/--
A problem of Erdős and Gimbel, who proved that there must exist a subgraph $H$ with
\[
\zeta(H) \gg \left(\frac{m}{\log m}\right)^{1/2}.
\]
-/
@[category research solved, AMS 5]
theorem erdos_760.variants.erdos_gimbel :
    ∃ c > (0 : ℝ), ∀ (V : Type*) [Finite V] (G : SimpleGraph V) (m : ℕ),
      G.chromaticNumber = (m : ℕ∞) →
        ∃ H : G.Subgraph, ∃ k : ℕ, ((k : ℕ∞) ≤ H.coe.cochromaticNumber) ∧
          (c * Real.sqrt ((m : ℝ) / Real.log (m : ℝ)) ≤ (k : ℝ)) := by
  sorry

end Erdos760
