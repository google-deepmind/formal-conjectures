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
# Erdős Problem 876

*Reference:* [erdosproblems.com/876](https://www.erdosproblems.com/876)

Let $A = \{a_1 < a_2 < \cdots\}$ be an infinite sum-free sequence (no element is the sum of
finitely many distinct smaller elements). Is it possible that $a_{n+1} - a_n < n$ for all
sufficiently large $n$? Graham proved there exists such a sequence with
$a_{n+1} - a_n < n^{1+o(1)}$.

Erdős proved that sum-free sets have density zero [Er62c], and later asked about the maximum
value of $\sum_{n \in A} 1/n$ [Er75b] [Er77c]. Deshouillers, Erdős, and Melfi constructed a
sum-free set with $a_n \sim n^{3+o(1)}$ [DEM99]. Łuczak and Schoen established bounds on the
density of sum-free sets [LuSc00].

Related: Problem 790.

[Er62c] Erdős, P., *Some remarks on number theory. III*, Mat. Lapok (1962), pp. 28–38.

[Er75b] Erdős, P., *Problems and results in combinatorial number theory*,
Journées Arithmétiques de Bordeaux (1975), pp. 295–310.

[Er77c] Erdős, P., *Problems and results on combinatorial number theory. III*,
Number theory day (1977), pp. 43–72.

[Er98] Erdős, P., *Some of my new and almost new problems and results in combinatorial
number theory*, Number theory (Eger, 1996) (1998), pp. 169–180.

[DEM99] Deshouillers, J.-M., Erdős, P., Melfi, G., *On a question about sum-free sequences*,
Discrete Math. (1999), pp. 49–54.

[LuSc00] Łuczak, T., Schoen, T., *On the maximal density of sum-free sets*,
Acta Arith. (2000), pp. 225–229.
-/

namespace Erdos876

/--
A set $A \subseteq \mathbb{N}$ is sum-free in the sense of Erdős if no element of $A$ can be
expressed as the sum of finitely many distinct smaller elements of $A$.
-/
def IsSumFreeErdos (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S.Nonempty → (∀ x ∈ S, x ∈ A) → (∀ x ∈ S, x < a) → S.sum id ≠ a

/--
Let $A = \{a_1 < a_2 < \cdots\} \subseteq \mathbb{N}$ be an infinite sum-free set (no element
is the sum of finitely many distinct smaller elements of $A$). Is it possible that
$a_{n+1} - a_n < n$ for all sufficiently large $n$?

Erdős notes that Graham proved there exists such a sequence with
$a_{n+1} - a_n < n^{1+o(1)}$.
-/
@[category research open, AMS 5 11]
theorem erdos_876 : answer(sorry) ↔
    ∃ a : ℕ → ℕ, StrictMono a ∧
      IsSumFreeErdos (Set.range a) ∧
      ∃ N, ∀ n ≥ N, a (n + 1) - a n < n + 1 := by
  sorry

/--
Graham proved that there exists an infinite sum-free set $A = \{a_1 < a_2 < \cdots\}$ such that
$a_{n+1} - a_n < n^{1+\varepsilon}$ for every $\varepsilon > 0$ and all sufficiently large $n$.
This is the best known result toward Problem 876 [Er98].
-/
@[category research solved, AMS 5 11]
theorem erdos_876_graham : ∃ a : ℕ → ℕ, StrictMono a ∧
    IsSumFreeErdos (Set.range a) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      (a (n + 1) - a n : ℝ) < (n : ℝ) ^ (1 + ε) := by
  sorry

end Erdos876
