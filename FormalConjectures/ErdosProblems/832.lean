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
# Erdős Problem 832

*References:*
- [erdosproblems.com/832](https://www.erdosproblems.com/832)
- [AkSh16] Akolzin, Ilia and Shabanov, Dmitry, Colorings of hypergraphs with large number of colors.
Discrete Math. (2016), 3020--3031.
- [Al85] Alon, Noga, Hypergraphs with high chromatic number. Graphs Combin. (1985), 387--389.
- [ChPe20] Cherkashin, Danila and Petrov, Fedor, Regular behavior of the maximal hypergraph
chromatic number. SIAM J. Discrete Math. (2020), 1326--1333.
-/

namespace Erdos832

open Filter Asymptotics

/--
Let $r\geq 3$ and $k$ be sufficiently large in terms of $r$. Is it true that every $r$-uniform
hypergraph with chromatic number $k$ has at least
$$\binom{(r-1)(k-1)+1}{r}$$
edges, with equality only for the complete graph on $(r-1)(k-1)+1$ vertices?

This was disproved by Alon [Al85]. The validity of this conjecture for $r=3$ remains open.
-/
@[category research solved, AMS 5]
theorem erdos_832 :
    answer(False) ↔ ∀ r : ℕ, 3 ≤ r → ∀ᶠ k : ℕ in atTop,
    ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
      H.IsUniform r → H.HasHypergraphChromaticNumber k →
      ((r - 1) * (k - 1) + 1).choose r ≤ H.card ∧
      (H.card = ((r - 1) * (k - 1) + 1).choose r →
        ∃ S : Finset (Fin n), S.card = (r - 1) * (k - 1) + 1 ∧ H = S.powersetCard r) := by
  sorry

end Erdos832
