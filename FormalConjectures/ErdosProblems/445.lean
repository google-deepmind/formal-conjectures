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
# Erdős Problem 445

*Reference:* [erdosproblems.com/445](https://www.erdosproblems.com/445)

Is it true that, for any $c > 1/2$, if $p$ is a sufficiently large prime then,
for any $n \geq 0$, there exist $a, b \in (n, n + p^c)$ such that
$ab \equiv 1 \pmod{p}$?

Heilbronn (unpublished) proved this for $c$ sufficiently close to $1$.
Heath-Brown [He00] used Kloosterman sums to prove this for all $c > 3/4$.
-/

open Real

namespace Erdos445

/-- Erdős Problem 445 (OPEN):
Is it true that, for any $c > 1/2$, if $p$ is a sufficiently large prime then for any $n \geq 0$
there exist $a, b \in (n, n + p^c)$ with $ab \equiv 1 \pmod{p}$? [He00] -/
@[category research open, AMS 11]
theorem erdos_445 : answer(sorry) ↔ ∀ (c : ℝ), c > 1 / 2 →
    ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p →
    ∀ n : ℕ, ∃ a b : ℕ,
    (n : ℝ) < (a : ℝ) ∧ (a : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    (n : ℝ) < (b : ℝ) ∧ (b : ℝ) < (n : ℝ) + (p : ℝ) ^ c ∧
    a * b ≡ 1 [MOD p] := by
  sorry

end Erdos445
