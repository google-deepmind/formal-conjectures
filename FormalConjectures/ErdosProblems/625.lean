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
- [ErGi93] P. Erdős and J. Gimbel, *Some problems and results in cochromatic theory*.
  Annals of Discrete Mathematics 55 (1993), 261–264.
- [Gi16] J. Gimbel, *Some of my favorite coloring problems for graphs and digraphs*.
  Graph Theory: Favorite Conjectures and Open Problems 1 (2016), 95–108.
- [He24c] A. Heckel, *The difference between the chromatic and the cochromatic number of a
  random graph* (2024), [arXiv:2409.17614](https://arxiv.org/abs/2409.17614).
- [Pe26] S. Petkov, *A Full-Sequence Quantitative Gap Between the Chromatic and Cochromatic
  Numbers of a Random Graph* (2026), [arXiv:2608.30604](https://arxiv.org/abs/2608.30604).
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

Here "almost surely $\chi(G)-\zeta(G)\to\infty$" is read in the usual random-graph sense: for
every fixed real threshold $K$, the probability that $\chi(G)-\zeta(G)\ge K$ tends to one along
the full sequence of natural numbers. The answer is yes. Heckel [He24c] proved this along a
subsequence of density about $0.95$; Petkov [Pe26] proves it along all $n$, with the
quantitative bound below.
-/
@[category research solved, question, AMS 5 60, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-02-000006"]
theorem erdos_625 :
    ∀ K : ℝ, Tendsto
      (fun n : ℕ ↦ binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
        {G | K ≤ (G.chromaticNumber.toNat : ℝ) - G.cochromaticNumber.toNat})
      atTop (𝓝 1) := by
  sorry

/--
Petkov [Pe26] proves that, for $G\sim G(n,1/2)$, the probability that
$$\chi(G)-\zeta(G)\geq
\frac{(\log 2)^2}{4}\log\!\left(\frac{200}{153}\right)\frac{n}{(\log n)^3}$$
tends to one as $n\to\infty$ along all natural numbers. All logarithms are natural.
-/
@[category research solved, AMS 5 60, formal_proof using lean4 at
  "https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-02-000006"]
theorem erdos_625.variants.quantitative :
    Tendsto
      (fun n : ℕ ↦ binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
        {G | ((Real.log 2) ^ 2 / 4 * Real.log (200 / 153 : ℝ)) *
            n / (Real.log n) ^ 3 ≤
          (G.chromaticNumber.toNat : ℝ) - G.cochromaticNumber.toNat})
      atTop (𝓝 1) := by
  sorry

end Erdos625
