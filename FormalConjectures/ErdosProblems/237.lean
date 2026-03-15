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
# Erdős Problem 237

*Reference:* [erdosproblems.com/237](https://www.erdosproblems.com/237)

Let $A \subseteq \mathbb{N}$ be a set such that $|A \cap \{1, \ldots, N\}| \gg \log N$ for all large $N$.
Let $f(n)$ count the number of solutions to $n = p + a$ for $p$ prime and $a \in A$.
Is it true that $\limsup f(n) = \infty$?

The answer is yes, as proved by Chen and Ding [ChDi22]. In fact, the
assumption $|A \cap \{1, \ldots, N\}| \gg \log N$ can be replaced with just the assumption
that $A$ is infinite. Erdős [Er50] had proved the result when $A = \{2^k : k \geq 0\}$.

[Er50] Erdős, P., _On integers of the form $2^k + p$ and some related problems_. Summa Brasil.
Math. **2** (1950), 113–123.

[Er55c] Erdős, P., _Some problems on number theory_ (1955).

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
**6** (1961), 221–254.

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A Survey of
Combinatorial Theory (1973), 117–138.

[ChDi22] Chen, Y.-G. and Ding, Y., _On a conjecture of Erdős_. arXiv:2201.10727 (2022).
-/

open Set Real

namespace Erdos237

/-- The number of representations of $n$ as $p + a$ where $p$ is prime and $a \in A$. -/
noncomputable def countRepresentations (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | Nat.Prime p ∧ p ≤ n ∧ (n - p) ∈ A}

/-- The counting function $|A \cap \{1, \ldots, N\}|$. -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/--
Erdős Problem 237 [Er50, Er55c, Er61, Er73] (proved by Chen–Ding [ChDi22]):

Let $A \subseteq \mathbb{N}$ with $|A \cap \{1, \ldots, N\}| \geq c \cdot \log N$ for some $c > 0$ and all
sufficiently large $N$. Let $f(n) = \#\{p \text{ prime} : n - p \in A\}$ count the
representations of $n$ as prime + element of $A$. Then $\limsup f(n) = \infty$,
i.e., for every $M$ there exist arbitrarily large $n$ with $f(n) \geq M$.

The conclusion is an unrolled form of $\limsup_{n \to \infty} f(n) = \infty$,
avoiding `Filter` machinery.
-/
@[category research solved, AMS 11]
theorem erdos_237 : answer(True) ↔
    (∀ A : Set ℕ,
    (∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countingFunction A N : ℝ) ≥ c * Real.log (N : ℝ)) →
    ∀ M : ℕ, ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ countRepresentations A n ≥ M) := by
  sorry

/--
Stronger form of Erdős Problem 237, proved by Chen–Ding [ChDi22]:

The growth hypothesis $|A \cap \{1, \ldots, N\}| \gg \log N$ can be weakened to
just requiring that $A$ is infinite. Then $\limsup f(n) = \infty$ still holds.
-/
@[category research solved, AMS 11]
theorem erdos_237_strong :
    (∀ A : Set ℕ, A.Infinite →
    ∀ M : ℕ, ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ countRepresentations A n ≥ M) := by
  sorry

end Erdos237
