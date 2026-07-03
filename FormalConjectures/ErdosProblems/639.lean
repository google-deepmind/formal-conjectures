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
# Erdős Problem 639

*References:*
- [erdosproblems.com/639](https://www.erdosproblems.com/639)
- [KeSu04] Keevash, Peter and Sudakov, Benny, *On the number of edges not covered by monochromatic
  copies of a fixed graph*. J. Combin. Theory Ser. B (2004), 41-53.
- [Py86] Pyber, L., *Clique covering of graphs*. Combinatorica (1986), 393-398.
-/

open Filter

namespace Erdos639

/--
Is it true that if the edges of $K_n$ are 2-coloured then there are at most $n^2/4$ many edges
which do not occur in a monochromatic triangle?

Solved by Erdős, Rousseau, and Schelp for large $n$, but unpublished. Alon has observed that this
also follows from a result of Pyber [Py86], which states that (for large enough $n$) at most
$\lfloor n^2/4\rfloor+2$ monochromatic cliques cover all edges of a $2$-coloured $K_n$.

This problem was solved completely by Keevash and Sudakov [KeSu04], who proved that the correct
threshold is $\lfloor n^2/4\rfloor$ for all $n\geq 7$, is $\binom{n}{2}$ for $n\leq 5$, and is
$10$ for $n=6$.

Since the bound fails for small $n$ (at $n=6$ the threshold is $10 > 6^2/4$), the statement is
formalized in the asymptotic reading in which the problem was posed and solved: for all
sufficiently large $n$, every $2$-colouring of the edges of $K_n$ leaves at most $n^2/4$ edges
not occurring in a monochromatic triangle. Edges of $K_n$ are the non-diagonal unordered pairs
`Sym2 (Fin n)`; an edge $\{x, y\}$ occurs in a monochromatic triangle if and only if there is a
third vertex $z$ with $C(\{x, z\}) = C(\{y, z\}) = C(\{x, y\})$.
-/
@[category research solved, AMS 5]
theorem erdos_639 : answer(True) ↔
    ∀ᶠ (n : ℕ) in atTop, ∀ C : Sym2 (Fin n) → Fin 2,
      {e : Sym2 (Fin n) | ¬e.IsDiag ∧
        ∀ x y : Fin n, e = s(x, y) →
          ¬∃ z, z ≠ x ∧ z ≠ y ∧ C s(x, z) = C e ∧ C s(y, z) = C e}.ncard ≤ n ^ 2 / 4 := by
  sorry

end Erdos639
