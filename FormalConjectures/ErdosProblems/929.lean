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
# Erdős Problem 929

For $k \geq 2$, let $S(k)$ be the minimal $x$ such that the set of $n$ with $n+1, \ldots, n+k$
all $x$-smooth has positive upper density. Erdős conjectured that $S(k) \geq k^{1-o(1)}$.

*Reference:* [erdosproblems.com/929](https://www.erdosproblems.com/929)

[Er76d] Erdős, P., *Problems in number theory and combinatorics*. Proceedings of the Sixth
Manitoba Conference on Numerical Mathematics (1976), 35-58.
-/

namespace Erdos929

/-- An integer $m$ is $x$-smooth if all its prime factors are at most $x$. -/
def IsSmooth (x m : ℕ) : Prop :=
  ∀ p ∈ m.primeFactors, p ≤ x

/-- The set of $n$ such that $n+1, n+2, \ldots, n+k$ are all $x$-smooth. -/
def smoothConsecutiveBlockSet (k x : ℕ) : Set ℕ :=
  {n : ℕ | ∀ i : ℕ, 1 ≤ i → i ≤ k → IsSmooth x (n + i)}

/-- A set $S \subseteq \mathbb{N}$ has positive upper density: there exists $\delta > 0$ such that
$|S \cap [1, N]| / N \geq \delta$ for infinitely many $N$. -/
noncomputable def HasPositiveUpperDensity (S : Set ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N ≥ N₀ ∧
    ((S ∩ {i | 1 ≤ i ∧ i ≤ N}).ncard : ℝ) / (N : ℝ) ≥ δ

/--
Erdős Problem 929 [Er76d]:

For $k \geq 2$, let $S(k)$ be the minimal $x$ such that the set of $n$ with
$n+1, \ldots, n+k$ all $x$-smooth has positive upper density. The conjecture is that
$S(k) \geq k^{1-o(1)}$, i.e., for every $\varepsilon > 0$ and all sufficiently large $k$,
if $x < k^{1-\varepsilon}$ then the set of $n$ with $n+1, \ldots, n+k$ all $x$-smooth does not
have positive upper density.
-/
@[category research open, AMS 11]
theorem erdos_929 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    ∀ x : ℕ, (x : ℝ) < (k : ℝ) ^ (1 - ε) →
    ¬HasPositiveUpperDensity (smoothConsecutiveBlockSet k x) := by
  sorry

end Erdos929
