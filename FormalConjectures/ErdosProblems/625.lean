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

/-!
# Erdős Problem 625

*References:*
- [erdosproblems.com/625](https://www.erdosproblems.com/625)
- [Gi16] J. Gimbel, *Some of my favorite coloring problems for graphs and digraphs*.
  Graph Theory: Favorite conjectures and open problems (2016), 95–108.
- [Pe26] S. Petkov, *A Full-Sequence Quantitative Gap Between the Chromatic and Cochromatic
  Numbers of a Random Graph*. [arXiv:2608.30604](https://arxiv.org/abs/2608.30604) (2026).
- [Formalization](https://github.com/SamPetkov/Erdos625-formalization), by Samuil Petkov,
  licensed under CC BY 4.0.
-/

@[expose] public section

open Filter SimpleGraph
open scoped Topology

namespace Erdos625

/--
The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed
to colour the vertices of $G$ such that each colour class induces either a complete graph or
empty graph. Let $\chi(G)$ denote the chromatic number.

If $G$ is a random graph with $n$ vertices and each edge included independently with
probability $1/2$ then is it true that almost surely $\chi(G)-\zeta(G)\to\infty$ as
$n\to\infty$?

Petkov [Pe26] proves a positive answer. Here the asymptotic probability statement means that,
for every fixed real threshold, the probability of being at least that threshold tends to one.
-/
@[category research solved, AMS 5 60, formal_proof using lean4 at
"https://github.com/SamPetkov/Erdos625-formalization/blob/9702b5e734627e3fdaef8da0d65ad7394016f0a7/Erdos625/Section15FinalInstantiation.lean#L22"]
theorem erdos_625 : answer(True) ↔
    ∀ K : ℝ, Tendsto
      (fun n : ℕ ↦ binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
        {G | K ≤ (G.chromaticNumber.toNat : ℝ) - G.cochromaticNumber.toNat})
      atTop (𝓝 1) := by
  sorry

/--
Petkov [Pe26] proves that, for $G\sim G(n,1/2)$, the probability that
$$\chi(G)-\zeta(G)\geq
\frac{(\log 2)^2}{4}\log\!\left(\frac{200}{153}\right)\frac{n}{(\log n)^3}$$
tends to one as $n\to\infty$. All logarithms are natural.
-/
@[category research solved, AMS 5 60, formal_proof using lean4 at
"https://github.com/SamPetkov/Erdos625-formalization/blob/9702b5e734627e3fdaef8da0d65ad7394016f0a7/Erdos625/Section15FinalInstantiation.lean#L22"]
theorem erdos_625.variants.quantitative :
    Tendsto
      (fun n : ℕ ↦ binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
        {G | ((Real.log 2) ^ 2 / 4 * Real.log (200 / 153 : ℝ)) *
            n / (Real.log n) ^ 3 ≤
          (G.chromaticNumber.toNat : ℝ) - G.cochromaticNumber.toNat})
      atTop (𝓝 1) := by
  sorry

end Erdos625
