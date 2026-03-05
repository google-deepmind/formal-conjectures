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
# Erdős Problem 788

*Reference:* [erdosproblems.com/788](https://www.erdosproblems.com/788)

Let $f(n)$ be maximal such that if $B \subset (2n, 4n) \cap \mathbb{N}$ there exists some
$C \subset (n, 2n) \cap \mathbb{N}$ such that $c_1 + c_2 \notin B$ for all
$c_1 \neq c_2 \in C$ and $|C| + |B| \geq f(n)$.

Estimate $f(n)$. In particular is it true that $f(n) \leq n^{1/2+o(1)}$?

A conjecture of Choi, who proved $f(n) \ll n^{3/4}$. Adenwalla provided a construction proving
$f(n) \gg n^{1/2}$. The bound $f(n) \ll (n \log n)^{2/3}$ was proved by Baltz, Schoen, and
Srivastav. The work of Alon and Pham on random Cayley graphs implies
$f(n) \leq n^{3/5+o(1)}$.

[AlPh25] Alon, N. and Pham, H.T., _Random Cayley graphs_.
-/

open Finset Real

namespace Erdos788

/-- $f(n)$: the largest $m$ such that for every $B \subseteq (2n, 4n) \cap \mathbb{N}$, there
exists $C \subseteq (n, 2n) \cap \mathbb{N}$ with $c_1 + c_2 \notin B$ for all distinct
$c_1, c_2 \in C$ and $|C| + |B| \geq m$. -/
noncomputable def erdos788F (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ B : Finset ℕ, B ⊆ Finset.Ioo (2 * n) (4 * n) →
    ∃ C : Finset ℕ, C ⊆ Finset.Ioo n (2 * n) ∧
      (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → c₁ + c₂ ∉ B) ∧
      C.card + B.card ≥ m}

/-- **Erdős Problem 788** — Is it true that $f(n) \leq n^{1/2+o(1)}$? That is, for every
$\varepsilon > 0$ there exists $N_0$ such that $f(n) \leq n^{1/2+\varepsilon}$ for all
$n \geq N_0$.

A conjecture of Choi, who proved $f(n) \ll n^{3/4}$. -/
@[category research open, AMS 5]
theorem erdos_788 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos788F n : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε) := by
  sorry

/-- Lower bound (Adenwalla): $f(n) \gg n^{1/2}$, i.e., there exists $C > 0$ such that
$f(n) \geq C \cdot n^{1/2}$ for all sufficiently large $n$. -/
@[category research solved, AMS 5]
theorem erdos_788.variants.lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos788F n : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/-- Upper bound (Alon–Pham [AlPh25]): $f(n) \leq n^{3/5+o(1)}$, i.e., for every
$\varepsilon > 0$ there exists $N_0$ such that $f(n) \leq n^{3/5+\varepsilon}$ for all
$n \geq N_0$. -/
@[category research solved, AMS 5]
theorem erdos_788.variants.upper :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos788F n : ℝ) ≤ (n : ℝ) ^ (3 / 5 + ε) := by
  sorry

end Erdos788
