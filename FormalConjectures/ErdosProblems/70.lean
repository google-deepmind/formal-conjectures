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
# Erdős Problem 70

*Reference:* [erdosproblems.com/70](https://www.erdosproblems.com/70)

Is it true that $\mathfrak{c} \to (\beta, n)^2_3$ for every countable ordinal $\beta$ and
every finite $n \geq 2$, where $\mathfrak{c}$ is the cardinality of the continuum?

[Er87] Erdős, P., *On some of my favourite unsolved problems* (1987).
-/

open Ordinal Cardinal

namespace Erdos70

/-- The ordinal partition relation $\alpha \to (\beta, \gamma)^2_3$:
for every 2-coloring of increasing triples from ordinals below $\alpha$,
there is either a homogeneous set of order type $\beta$ for color 0,
or a homogeneous set of order type $\gamma$ for color 1.

A homogeneous set of order type $\delta$ is given by a strictly increasing
function $g$ mapping ordinals below $\delta$ to ordinals below $\alpha$, such that
all increasing triples in the image of $g$ receive the same color. -/
def OrdinalPartition3_2 (α β γ : Ordinal) : Prop :=
  ∀ f : Ordinal → Ordinal → Ordinal → Fin 2,
    (∃ g : Ordinal → Ordinal,
      (∀ i j, i < β → j < β → i < j → g i < g j) ∧
      (∀ i, i < β → g i < α) ∧
      ∀ i j k, i < j → j < k → k < β → f (g i) (g j) (g k) = 0) ∨
    (∃ g : Ordinal → Ordinal,
      (∀ i j, i < γ → j < γ → i < j → g i < g j) ∧
      (∀ i, i < γ → g i < α) ∧
      ∀ i j k, i < j → j < k → k < γ → f (g i) (g j) (g k) = 1)

/--
**Erdős Problem #70** [Er87]:

Let $\mathfrak{c}$ be the cardinality of the continuum (viewed as an initial ordinal),
$\beta$ be any countable ordinal, and $2 \le n < \omega$. Is it true that
$\mathfrak{c} \to (\beta, n)^2_3$?
-/
@[category research open, AMS 3 5]
theorem erdos_70 : answer(sorry) ↔
    ∀ (β : Ordinal), β.card ≤ ℵ₀ → ∀ (n : ℕ), 2 ≤ n →
      OrdinalPartition3_2 (Cardinal.continuum.ord) β (↑n) := by
  sorry

end Erdos70
