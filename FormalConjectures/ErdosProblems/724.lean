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
# Erdős Problem 724

*Reference:* [erdosproblems.com/724](https://www.erdosproblems.com/724)

Let $f(n)$ be the maximum number of mutually orthogonal Latin squares of order $n$.
Is it true that $f(n) \gg n^{1/2}$?

A Latin square of order $n$ is an $n \times n$ array filled with $n$ symbols such that
each symbol occurs exactly once in each row and each column.

Two Latin squares $L_1$, $L_2$ of order $n$ are orthogonal if the map
$(i, j) \mapsto (L_1(i,j), L_2(i,j))$ is injective (equivalently bijective) on
$\{1, \ldots, n\}^2$, i.e., every ordered pair of symbols occurs exactly once
when the squares are superimposed.

[Er81] Erdős, P., 1981.

[CES60] Chowla, S., Erdős, P., and Straus, E.G., on the maximal number of pairwise
orthogonal Latin squares of a given order, 1960.

[Wi74] Wilson, R.M., Concerning the number of mutually orthogonal Latin squares, 1974.

[Be83c] Beth, T., A remark on the number of mutually orthogonal Latin squares, 1983.
-/

namespace Erdos724

/-- A Latin square of order $n$: a function `Fin n → Fin n → Fin n` such that
each row and each column is a bijection. -/
def IsLatinSquare {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i : Fin n, Function.Bijective (L i)) ∧
  (∀ j : Fin n, Function.Bijective (fun i => L i j))

/-- Two Latin squares of order $n$ are orthogonal if the map
$(i, j) \mapsto (L_1(i,j), L_2(i,j))$ is injective on `Fin n × Fin n`. -/
def AreOrthogonalLatinSquares {n : ℕ} (L₁ L₂ : Fin n → Fin n → Fin n) : Prop :=
  Function.Injective (fun p : Fin n × Fin n => (L₁ p.1 p.2, L₂ p.1 p.2))

/-- A family of $k$ Latin squares of order $n$ is mutually orthogonal if each
is a Latin square and every distinct pair is orthogonal. -/
def IsMOLS {n k : ℕ} (L : Fin k → Fin n → Fin n → Fin n) : Prop :=
  (∀ i : Fin k, IsLatinSquare (L i)) ∧
  (∀ i j : Fin k, i ≠ j → AreOrthogonalLatinSquares (L i) (L j))

/-- The maximum number of mutually orthogonal Latin squares of order $n$. -/
noncomputable def maxMOLS (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ L : Fin k → Fin n → Fin n → Fin n, IsMOLS L}

/--
Erdős Problem 724 [Er81]:

Let $f(n)$ be the maximum number of mutually orthogonal Latin squares of order $n$.
Is it true that $f(n) \gg n^{1/2}$?

Chowla, Erdős, and Straus [CES60] proved $f(n) \gg n^{1/91}$.
Wilson [Wi74] improved this to $f(n) \gg n^{1/17}$.
Beth [Be83c] improved this to $f(n) \gg n^{1/14.8}$.
-/
@[category research open, AMS 5]
theorem erdos_724 : answer(sorry) ↔ ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    (maxMOLS n : ℝ) ≥ C * Real.sqrt (n : ℝ) := by
  sorry

end Erdos724
