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
# Erdős Problem 487

*Reference:* [erdosproblems.com/487](https://www.erdosproblems.com/487)

If $A \subseteq \mathbb{N}$ has positive upper density, must there exist distinct
$a, b, c \in A$ such that $\text{lcm}(a, b) = c$?

[Er61] Erdős, P., _Graph theory and probability. II_. Canad. J. Math. 13 (1961), p. 236.

[Er65b] Erdős, P., _Extremal problems in number theory_. Proc. Sympos. Pure Math. 8 (1965),
p. 228.

[Kl71] Kleitman, D., _On a combinatorial conjecture of Erdős_. J. Combin. Theory Ser. A 1
(1971).
-/

open Finset

namespace Erdos487

/--
A set $A \subseteq \mathbb{N}$ has positive upper density if there exists $\delta > 0$ such that
for arbitrarily large $N$, $|A \cap \{1, \ldots, N\}| / N \geq \delta$.
-/
noncomputable def HasPositiveUpperDensity487 (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
    ((A ∩ {i | 1 ≤ i ∧ i ≤ N}).ncard : ℝ) ≥ δ * (N : ℝ)

/--
Erdős Problem 487 [Er61, p. 236] [Er65b, p. 228]:

Let $A \subseteq \mathbb{N}$ have positive upper density. Must there exist distinct
$a, b, c \in A$ such that $[a, b] = c$ (where $[a, b]$ denotes the least common multiple of
$a$ and $b$)?

This is true, a consequence of the positive solution to Erdős Problem 447
by Kleitman [Kl71].
-/
@[category research solved, AMS 5 11]
theorem erdos_487 : answer(True) ↔
    ∀ (A : Set ℕ), HasPositiveUpperDensity487 A →
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Nat.lcm a b = c := by
  sorry

end Erdos487
