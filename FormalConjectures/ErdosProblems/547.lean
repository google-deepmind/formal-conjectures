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
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Erdős Problem 547

*Reference:* [erdosproblems.com/547](https://www.erdosproblems.com/547)

If $T$ is a tree on $n$ vertices then $R(T) \leq 2n - 2$.

This was conjectured by Burr [Bu74]. It follows from the Erdős–Sós
conjecture [548], and has been proved for all large $n$ by Zhao [Zh11].

[Bu74] Burr, S. A., _Generalized Ramsey theory for graphs — a survey_.
(1974), 52-75.

[Zh11] Zhao, Y., _Proof of the (n/2-n/2-n/2) conjecture for large n_.
Electronic Journal of Combinatorics (2011), Paper 27, 61 pages.
-/

open SimpleGraph

namespace Erdos547

/-- The diagonal Ramsey number $R(G)$ for a graph $G$: the minimum $N$
such that every graph $H$ on $N$ vertices contains a copy of $G$ or its complement contains
a copy of $G$. -/
noncomputable def ramseyNumber {U : Type*} (G : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    G.IsContained H ∨ G.IsContained Hᶜ}

/--
Erdős Problem 547 [Bu74]:

If $T$ is a tree on $n$ vertices then $R(T) \leq 2n - 2$.
-/
@[category research open, AMS 5]
theorem erdos_547 (n : ℕ) (hn : n ≥ 2)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    ramseyNumber T ≤ 2 * n - 2 := by
  sorry

end Erdos547
