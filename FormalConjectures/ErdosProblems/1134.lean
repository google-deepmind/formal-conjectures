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
# Erdős Problem 1134

*Reference:* [erdosproblems.com/1134](https://www.erdosproblems.com/1134)

Let $A \subseteq \mathbb{N}$ be the smallest set which contains $1$ and is closed under the
operations $x \mapsto 2x+1$, $x \mapsto 3x+1$, and $x \mapsto 6x+1$. Does $A$ have positive
lower density?

This was disproved by Crampin and Hilton, who showed that
$|A \cap [1,X]| \ll X^{\tau+o(1)}$ where $\tau \approx 0.900626 < 1$ is the unique positive
root of $6^{-\tau} + \sum_{k \geq 0} (3 \cdot 2^k)^{-\tau} = 1$. In particular, $A$ has
density $0$.

[La16] Lau, D., *Function algebras on finite sets*. Springer Monographs in Mathematics (2016).
-/

open Filter

open scoped Topology

namespace Erdos1134

/-- The set $A$ from Erdős Problem 1134: the smallest subset of $\mathbb{N}$ containing $1$
and closed under $x \mapsto 2x+1$, $x \mapsto 3x+1$, and $x \mapsto 6x+1$. -/
inductive InSet : ℕ → Prop where
  | base : InSet 1
  | step2 (n : ℕ) : InSet n → InSet (2 * n + 1)
  | step3 (n : ℕ) : InSet n → InSet (3 * n + 1)
  | step6 (n : ℕ) : InSet n → InSet (6 * n + 1)

noncomputable instance : DecidablePred InSet := Classical.decPred _

/-- The counting function: $|A \cap [1, N]|$ for the set $A$ from Problem 1134. -/
noncomputable def count (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => InSet n)).card

/--
Erdős Problem 1134 [La16]:

Let $A \subseteq \mathbb{N}$ be the smallest set containing $1$ and closed under $x \mapsto 2x+1$,
$x \mapsto 3x+1$, and $x \mapsto 6x+1$. Does $A$ have positive lower density?

Disproved (answered in the negative) by Crampin and Hilton, who showed
$|A \cap [1,X]| \ll X^{\tau+o(1)}$ where $\tau \approx 0.900626 < 1$.
-/
@[category research solved, AMS 11]
theorem erdos_1134 : answer(False) ↔
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ (N : ℕ) in atTop,
      c ≤ (count N : ℝ) / (N : ℝ)) := by sorry

end Erdos1134
