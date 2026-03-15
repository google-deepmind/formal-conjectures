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
# Erdős Problem 185

*Reference:* [erdosproblems.com/185](https://www.erdosproblems.com/185)

Let $f_3(n)$ be the maximal size of a subset of $\{0,1,2\}^n$ which contains no three
points on a line. Is it true that $f_3(n) = o(3^n)$?

Originally considered by Moser. It is trivial that $f_3(n) \ge R_3(3^n)$, the maximal
size of a subset of $\{1,\ldots,3^n\}$ without a three-term arithmetic progression.
Moser showed that $f_3(n) \gg 3^n / \sqrt{n}$. The answer is yes, which is a corollary of
the density Hales-Jewett theorem, proved by Furstenberg and Katznelson [FuKa91].

[Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo.,
1971) (1973), 117-138.

[FuKa91] Furstenberg, H. and Katznelson, Y., *A density version of the Hales-Jewett
theorem*. J. Anal. Math. 57 (1991), 64-119.

OEIS: [A003142](https://oeis.org/A003142)
-/

namespace Erdos185

/-- A combinatorial line in $\{0,1,2\}^n$ consists of three points parameterized by
$j \in \{0,1,2\}$, such that there exists a nonempty set $S$ of "active" coordinates
where the $j$-th point has value $j$ at each active coordinate, and all three points
agree at non-active coordinates. -/
def IsCombinatorialLine (n : ℕ) (p : Fin 3 → (Fin n → Fin 3)) : Prop :=
  ∃ (S : Finset (Fin n)), S.Nonempty ∧
    ∃ (c : Fin n → Fin 3),
      ∀ (j : Fin 3) (i : Fin n),
        p j i = if i ∈ S then j else c i

/--
Erdős Problem 185 (Density Hales-Jewett for $k=3$) [Er73]:

For every $\varepsilon > 0$, there exists $N$ such that for all $n \ge N$, every subset
$A \subseteq \{0,1,2\}^n$ of size $|A| > \varepsilon \cdot 3^n$ contains a combinatorial
line (three points on a line).

Equivalently, the maximum size $f_3(n)$ of a line-free subset of $\{0,1,2\}^n$ satisfies
$f_3(n) = o(3^n)$.
-/
@[category research solved, AMS 5]
theorem erdos_185 :
    answer(True) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ A : Finset (Fin n → Fin 3),
            (A.card : ℝ) > ε * (3 : ℝ) ^ n →
            ∃ p : Fin 3 → (Fin n → Fin 3),
              IsCombinatorialLine n p ∧ ∀ j : Fin 3, p j ∈ A := by
  sorry

end Erdos185
