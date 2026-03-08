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
# Babai–Seress Conjectures on the Diameter of Finite Groups

*References:*
- [Wikipedia, *Diameter (group theory)*](https://en.wikipedia.org/wiki/Diameter_(group_theory))
- [H. A. Helfgott and Á. Seress, *On the diameter of permutation groups*](https://arxiv.org/abs/1109.3550)
- [L. Babai and Á. Seress, *On the diameter of permutation groups*,
  European Journal of Combinatorics 13 (1992), 231–243](https://doi.org/10.1016/S0195-6698(05)80029-0)

This file contains two conjectures from the Babai–Seress paper:

- **Conjecture 1.5**: $\operatorname{diam}(A_n) < n^C$ for some absolute constant $C$,
  where $A_n$ is the alternating group on $n$ elements.

- **Conjecture 1.7**: $\operatorname{diam}(G) < (\log |G|)^C$ for some absolute constant $C$,
  where $G$ ranges over all non-abelian finite simple groups.

Conjecture 1.7 generalises Conjecture 1.5, since for $G = A_n$ we have
$\log |A_n| \approx n \log n$, so a polylogarithmic bound in $|G|$ implies a polynomial
bound in $n$.
-/

namespace BabaiSeressConjectures

/-- The Cayley graph of a group $G$ with respect to a set $S$. Two elements $g, h \in G$ are
adjacent iff $g^{-1} h \in S$ (or equivalently $h^{-1} g \in S$ when $S$ is symmetric).

This is constructed using `SimpleGraph.fromRel`, which takes the relation
$g \sim h \iff g^{-1} h \in S$ and automatically symmetrizes it (via disjunction with the
reverse relation) and enforces irreflexivity (via $g \neq h$). -/
def cayleyGraph {G : Type*} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun g h => g⁻¹ * h ∈ S)

/-- **Babai–Seress Conjecture (Conjecture 1.5)**: There exists an absolute constant $C$ such
that for every $n$ and every symmetric generating set $S$ of the alternating group $A_n$,
the diameter of the Cayley graph satisfies
$$\operatorname{diam}(\operatorname{Cay}(A_n, S)) \leq n^C.$$

*Reference:* [L. Babai and Á. Seress, *On the diameter of permutation groups*,
European Journal of Combinatorics 13 (1992), Conjecture 1.5](https://doi.org/10.1016/S0195-6698(05)80029-0) -/
@[category research open, AMS 5 20 68]
theorem babai_seress_conjecture_alternating :
    ∃ C : ℕ, ∀ n : ℕ,
    ∀ S : Set (alternatingGroup (Fin n)),
    -- S is symmetric
    (∀ s ∈ S, s⁻¹ ∈ S) →
    -- S generates Aₙ
    Subgroup.closure S = ⊤ →
    ((cayleyGraph S).diam : ℝ) ≤ (n : ℝ) ^ C := by
  sorry

/-- **Babai–Seress Conjecture (Conjecture 1.7)**: There exists an absolute constant $C$ such
that for every finite simple non-abelian group $G$ and every symmetric generating set $S$
of $G$, the diameter of the Cayley graph $\operatorname{Cay}(G, S)$ satisfies
$$\operatorname{diam}(\operatorname{Cay}(G, S)) \leq (\log |G|)^C.$$

*Reference:* [L. Babai and Á. Seress, *On the diameter of permutation groups*,
European Journal of Combinatorics 13 (1992), Conjecture 1.7](https://doi.org/10.1016/S0195-6698(05)80029-0) -/
@[category research open, AMS 5 20 68]
theorem babai_seress_conjecture :
    ∃ C : ℕ,
    ∀ (G : Type) [Group G] [Fintype G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) →
    ∀ S : Set G,
    -- S is symmetric
    (∀ s ∈ S, s⁻¹ ∈ S) →
    -- S generates G
    Subgroup.closure S = ⊤ →
    ((cayleyGraph S).diam : ℝ) ≤ (Real.log (Fintype.card G : ℝ)) ^ C := by
  sorry

end BabaiSeressConjectures
