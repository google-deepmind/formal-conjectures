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
# Melnikov's valency-variety problem

*References:*
- [Open Problem Garden](https://www.openproblemgarden.org/op/melnikovs_valency_variety_problem)
- Jensen, T. R. and Toft, B., *Graph Coloring Problems*. Wiley (1995), p. 90.
- Zykov, A. A., Problem 11. *Beiträge zur Graphentheorie* (1968), p. 228.
-/

@[expose] public section

namespace MelnikovValencyVariety

open SimpleGraph

/-- The valency-variety $w(G)$ is the number of distinct vertex degrees of $G$. -/
def valencyVariety {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image fun v => G.degree v).card

/-- The proposed lower bound $\lceil\lfloor w(G)/2\rfloor/(|V(G)|-w(G))\rceil$.
For a simple graph with at least two vertices, $w(G) < |V(G)|$: degrees $0$ and $|V(G)|-1$
cannot both occur, so the denominator is positive. -/
def melnikovBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  let n := Fintype.card V
  let w := valencyVariety G
  ⌈(((w / 2 : ℕ) : ℚ≥0) / ((n - w : ℕ) : ℚ≥0))⌉₊

/-- Is the chromatic number of every finite simple graph with at least two vertices strictly
greater than $\lceil\lfloor w(G)/2\rfloor/(|V(G)|-w(G))\rceil$?
The answer is no: Kitamura gives a $37$-vertex graph with $w(G)=30$ and chromatic number $3$,
for which the proposed bound is also $3$. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/KitaKen1/opg-melnikov-valency-variety-lean/blob/eaeb21c4a46e872dc5b1790eeb63b284d5bcf3c1/lean/MelnikovValencyVarietyFC.lean#L91"]
theorem melnikov_valency_variety_problem :
    answer(False) ↔
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        2 ≤ Fintype.card V → (melnikovBound G : ℕ∞) < G.chromaticNumber := by
  sorry

end MelnikovValencyVariety
