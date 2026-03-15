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
# Erdős Problem 879

Let $G(n)$ denote the maximum sum of a pairwise coprime subset of $\{1, \ldots, n\}$,
and let $H(n) = \sum_{p < n} p + n \cdot \pi(\sqrt{n})$. Erdős and Van Lint asked
whether $G(n) > H(n) - n^{1+\varepsilon}$ for every $\varepsilon > 0$ and all
sufficiently large $n$ (Part 1), and whether for every $k \geq 2$ the optimal
admissible set must contain an element with at least $k$ distinct prime factors (Part 2).

Erdős and Van Lint proved that $H(n) - n^{3/2-o(1)} < G(n) < H(n)$ and
$(H(n) - G(n))/n \to \infty$. They also verified Part 2 for $k = 2$.

*Reference:* [erdosproblems.com/879](https://www.erdosproblems.com/879)

## References

* [Er84e] Erdős, P., _On two unconventional number theoretic functions and on some
  related problems_. (1984), 113–121.
* [Er98] Erdős, P., _Some of my new and almost new problems and results in
  combinatorial number theory_. Number theory (Eger, 1996) (1998), 169–180.

## See also

* [Problem 878](https://www.erdosproblems.com/878)
* OEIS sequence [A186736](https://oeis.org/A186736)
-/

namespace Erdos879

/-- An admissible subset of $\{1, \ldots, n\}$ that achieves the maximum sum among all
pairwise coprime subsets of $\{1, \ldots, n\}$. -/
def IsMaxAdmissible (S : Finset ℕ) (n : ℕ) : Prop :=
  S ⊆ Finset.Icc 1 n ∧ (↑S : Set ℕ).Pairwise Nat.Coprime ∧
  ∀ T : Finset ℕ, T ⊆ Finset.Icc 1 n → (↑T : Set ℕ).Pairwise Nat.Coprime →
    T.sum id ≤ S.sum id

/-- $H(n) = \sum_{p < n,\, p \text{ prime}} p + n \cdot \pi(\sqrt{n})$. -/
noncomputable def H (n : ℕ) : ℕ :=
  ((Finset.range n).filter Nat.Prime).sum id +
  n * ((Finset.range (Nat.sqrt n + 1)).filter Nat.Prime).card

/--
Erdős Problem 879, Part 1 [Er84e, Er98]:
For every $\varepsilon > 0$, for all sufficiently large $n$,
$G(n) > H(n) - n^{1+\varepsilon}$.
-/
@[category research open, AMS 5 11]
theorem erdos_879 :
    answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ S : Finset ℕ, IsMaxAdmissible S n →
    (↑(S.sum id) : ℝ) > (↑(H n) : ℝ) - (↑n : ℝ) ^ ((1 : ℝ) + ε) := by
  sorry

/--
Erdős Problem 879, Part 2 [Er84e, Er98]:
For every $k \geq 2$, if $n$ is sufficiently large then any admissible set maximising
$G(n)$ contains at least one integer with at least $k$ distinct prime factors.
-/
@[category research open, AMS 5 11]
theorem erdos_879.variants.prime_factors :
    answer(sorry) ↔
    ∀ k : ℕ, k ≥ 2 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ S : Finset ℕ, IsMaxAdmissible S n →
    ∃ a ∈ S, a.primeFactors.card ≥ k := by
  sorry

end Erdos879
