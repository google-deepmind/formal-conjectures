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
# Erdős Problem 425

Let $F(n)$ be the maximum size of a multiplicative Sidon subset of $\{1, \ldots, n\}$
(where all pairwise products are distinct). The problem asks whether the error term
$F(n) - \pi(n)$ has a precise asymptotic of the form $c \cdot n^{3/4} (\log n)^{-3/2}$
for some constant $c > 0$, and poses a generalization to $r$-fold products.

*Reference:* [erdosproblems.com/425](https://www.erdosproblems.com/425)

[Er68] Erdős, P., _On some applications of graph theory to number theoretic problems_. Publ.
Ramanujan Inst. (1968/69), 131-136.

[Er69] Erdős, P., _On some applications of graph theory to number theoretic problems_. Publ.
Ramanujan Inst. 1 (1969), 131-136.

[Er70b] Erdős, P., _Some applications of graph theory to number theory_. Proc. Second Chapel Hill
Conf. on Combinatorial Mathematics and its Applications (1970), 136-145.

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A Survey of
Combinatorial Theory (1973), 117-138.

[Er77c] Erdős, P., _Problems and results on combinatorial number theory. III._. Number Theory Day
(Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.

[Er80] Erdős, P., _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
(1980), 89-115.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter

namespace Erdos425

/--
A finite set $A \subseteq \mathbb{N}$ is a *multiplicative $B_2$ set* (or multiplicative Sidon set)
if whenever $ab = cd$ for $a, b, c, d \in A$ with $a < b$ and $c < d$, then $a = c$ and $b = d$.
Equivalently, the pairwise products $\{ab : a, b \in A, a < b\}$ are all distinct.
-/
def IsMultB2 (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a < b → c < d → a * b = c * d → a = c ∧ b = d

/--
A finite set $A \subseteq \mathbb{N}$ is an *$r$-multiplicative Sidon set* if any two $r$-element
subsets of $A$ with equal products must be the same subset.
-/
def IsMultBr (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.card = r → T.card = r →
    S.prod id = T.prod id → S = T

/--
$F(n)$ is the maximum cardinality of a multiplicative $B_2$ subset of $\{1, \ldots, n\}$.
-/
noncomputable def multB2MaxSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, IsMultB2 A ∧ (∀ x ∈ A, 1 ≤ x ∧ x ≤ n) ∧ A.card = k}

/--
Let $F(n)$ be the maximum size of a multiplicative $B_2$ subset of $\{1, \ldots, n\}$
(a set where all pairwise products $ab$ with $a < b$ are distinct).

Erdős [Er68] proved that there exist constants $0 < c_1 \leq c_2$ such that
$$
  \pi(n) + c_1 n^{3/4} (\log n)^{-3/2} \leq F(n) \leq \pi(n) + c_2 n^{3/4} (\log n)^{-3/2}.
$$

The conjecture asks whether there exists a constant $c$ such that
$$
  F(n) = \pi(n) + (c + o(1))\, n^{3/4} (\log n)^{-3/2},
$$
i.e., whether the ratio $(F(n) - \pi(n)) / (n^{3/4} / (\log n)^{3/2})$ converges.
-/
@[category research open, AMS 5 11]
theorem erdos_425 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
      Tendsto
        (fun n : ℕ =>
          ((multB2MaxSize n : ℝ) - (Nat.primeCounting n : ℝ)) /
          ((n : ℝ) ^ ((3 : ℝ) / 4) / (Real.log (n : ℝ)) ^ ((3 : ℝ) / 2)))
        atTop
        (nhds c) := by
  sorry

/--
If $A \subseteq \{1, \ldots, n\}$ is such that all products $a_1 \cdots a_r$ are distinct for
$a_1 < \cdots < a_r$ (i.e., $A$ is an $r$-multiplicative Sidon set), then
$$
  |A| \leq \pi(n) + O(n^{(r+1)/(2r)}).
$$
-/
@[category research open, AMS 5 11]
theorem erdos_425.variants.part2 : answer(sorry) ↔
    ∀ r : ℕ, 2 ≤ r →
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, ∀ A : Finset ℕ,
        (∀ x ∈ A, 1 ≤ x ∧ x ≤ n) →
        IsMultBr r A →
        (A.card : ℝ) ≤ (Nat.primeCounting n : ℝ) +
          C * (n : ℝ) ^ (((r : ℝ) + 1) / (2 * (r : ℝ))) := by
  sorry

end Erdos425
