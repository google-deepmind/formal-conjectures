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
# Erdős Problem 490

If $A, B \subseteq \{1, \ldots, N\}$ are such that all products $ab$ ($a \in A$, $b \in B$)
are distinct, is it true that $|A| \cdot |B| \ll N^2 / \log N$?

*Reference:* [erdosproblems.com/490](https://www.erdosproblems.com/490)

See also Problems 425 and 896.

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
**6** (1961), 221–254.

[Er69] Erdős, P., _On some applications of graph theory to number theoretic problems_. Publ.
Ramanujan Inst. 1 (1969), 131-136.

[Er72] Erdős, P., _Quelques problèmes de théorie des nombres_, p. 81, 1972.

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A Survey of
Combinatorial Theory (1973), 117-138.

[Sz76] Szemerédi, E., _On a problem of P. Erdős_. J. Number Theory (1976), 264-270.
-/

namespace Erdos490

/--
The products $ab$ with $a \in A$ and $b \in B$ are all distinct: the multiplication
map $A \times B \to \mathbb{N}$ is injective.
-/
def HasDistinctProducts (A B : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
    a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂

/--
If $A, B \subseteq \{1, \ldots, N\}$ are such that all products $ab$ ($a \in A$, $b \in B$)
are distinct, then $|A| \cdot |B| \ll N^2 / \log N$.

Formally: there exists a constant $C > 0$ such that for all $N \geq 2$ and all
$A, B \subseteq \{1, \ldots, N\}$ with distinct products,
$$
  |A| \cdot |B| \le C \cdot \frac{N^2}{\log N}.
$$

Proved by Szemerédi [Sz76].
-/
@[category research solved, AMS 5 11]
theorem erdos_490 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (N : ℕ), 2 ≤ N →
        ∀ (A B : Finset ℕ),
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
        HasDistinctProducts A B →
        (A.card : ℝ) * (B.card : ℝ) ≤ C * ((N : ℝ) ^ 2 / Real.log (N : ℝ)) := by
  sorry

/--
Does the limit $\lim_{N \to \infty} \max_{A,B \subseteq [N]} |A| |B| \log N / N^2$ exist,
where the maximum is over $A, B$ with distinct products? If it exists, it must be $\geq 1$.

This variant captures the question of whether the constant in Szemerédi's bound is sharp
and whether the limit exists at all. Posed by Erdős [Er72].
-/
@[category research open, AMS 5 11]
theorem erdos_490_limit :
    ∃ L : ℝ, L ≥ 1 ∧
      Filter.Tendsto
        (fun N : ℕ =>
          sSup {(A.card : ℝ) * (B.card : ℝ) * Real.log (N : ℝ) / ((N : ℝ) ^ 2) |
            (A : Finset ℕ) (B : Finset ℕ)
            (_ : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N)
            (_ : ∀ b ∈ B, 1 ≤ b ∧ b ≤ N)
            (_ : HasDistinctProducts A B)})
        Filter.atTop (nhds L) := by
  sorry

end Erdos490
