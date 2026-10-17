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
# The Balister–Győri–Schelp conjecture

*References:*
- [Perfect Matchings with Prescribed Differences Beyond Hall: The Two-Hole Problem](https://arxiv.org/abs/2607.08630)
  by *Aryeh Lev Zabokritskiy (Yohananov)* (2026)
- [Coloring vertices and edges of a graph by nonempty subsets of a set](https://doi.org/10.1016/j.ejc.2010.11.008)
  by *P. N. Balister, E. Győri, and R. H. Schelp*, European Journal of Combinatorics 32(4),
  533–537 (2011)
-/

namespace Arxiv.«2607.08630»

/--
The **Balister–Győri–Schelp conjecture** ([Conjecture 1](https://arxiv.org/pdf/2607.08630#page=6)):
for $s \ge 2$, every zero-sum list of $2^{s-1}$ nonzero vectors in $\mathbb{F}_2^s$ is the
prescribed-difference profile of a perfect matching of $\mathbb{F}_2^s$.

The equivalence $e$ indexes the two endpoints of each pair and ensures that the pairs are disjoint
and exhaust the ambient vector space.
-/
@[category research open, AMS 5]
theorem balister_gyori_schelp_conjecture (s : ℕ) (hs : 2 ≤ s)
    (v : Fin (2 ^ (s - 1)) → 𝔽₂ s)
    (hv_nonzero : ∀ i, v i ≠ 0)
    (hv_sum : ∑ i, v i = 0) :
    ∃ e : Fin (2 ^ (s - 1)) × Fin 2 ≃ 𝔽₂ s,
      ∀ i, e (i, 0) + e (i, 1) = v i := by
  sorry

end Arxiv.«2607.08630»
