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
# Erdős Problem 1169

Erdős and Hajnal asked whether for all finite $k < \omega$, the ordinal partition
relation $\omega_1^2 \to (\omega_1^2, k)^2$ fails.

*Reference:* [erdosproblems.com/1169](https://www.erdosproblems.com/1169)
-/

open Ordinal Cardinal

namespace Erdos1169

/-- $\omega_1$, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- The ordinal partition relation $\alpha \to (\beta, \gamma)^2$ for 2-colorings of pairs.
    For every 2-coloring of the pairs of ordinals below $\alpha$, there is either
    a homogeneous set of order type $\beta$ in color 0, or a homogeneous set of
    order type $\gamma$ in color 1. Formalized via strictly monotone embeddings:
    a subset of order type $\beta$ corresponds to a strictly monotone function
    from $\{x \mid x < \beta\}$ to $\{x \mid x < \alpha\}$. -/
def OrdinalPartitionPair (α β γ : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < α} → {x : Ordinal // x < α} → Bool,
    (∃ g : {x : Ordinal // x < β} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < β}, i < j → f (g i) (g j) = true) ∨
    (∃ g : {x : Ordinal // x < γ} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < γ}, i < j → f (g i) (g j) = false)

/--
Erdős Problem #1169 (Erdős and Hajnal):

Is it true that, for all finite $k < \omega$,
$$\omega_1^2 \not\to (\omega_1^2, k)^2?$$

That is, for every natural number $k$, there exists a 2-coloring of the pairs
of ordinals below $\omega_1^2$ such that no subset of order type $\omega_1^2$ is monochromatic
in the first color and no subset of order type $k$ is monochromatic in the
second color.

Hajnal proved this holds assuming the Continuum Hypothesis.
The problem is "not disprovable": open in ZFC, but true in some models.
-/
@[category research open, AMS 3 5]
theorem erdos_1169 : answer(sorry) ↔
    ∀ k : ℕ, ¬ OrdinalPartitionPair (omega1 ^ 2) (omega1 ^ 2) (↑k) := by
  sorry

end Erdos1169
