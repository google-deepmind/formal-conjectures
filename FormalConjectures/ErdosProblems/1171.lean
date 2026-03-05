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
# Erdős Problem 1171

*Reference:* [erdosproblems.com/1171](https://www.erdosproblems.com/1171)

Erdős asked whether for all finite $k$, the ordinal partition relation
$\omega_1^2 \to (\omega_1 \cdot \omega, 3, \ldots, 3)^2_{k+1}$ holds — that is, every
$(k+1)$-coloring of pairs below $\omega_1^2$ yields either a homogeneous set of order type
$\omega_1 \cdot \omega$ for the first color or a monochromatic triple for some other color.

- [Va99] Section 7.84.
- [Ba89b] Baumgartner.
-/

open Ordinal Cardinal

namespace Erdos1171

/-- $\omega_1$, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- The multi-color ordinal partition relation
$\alpha \to (\beta_0, \beta_1, \ldots, \beta_1)^2$ with $(k+1)$ colors.
For every $(k+1)$-coloring of pairs of ordinals below $\alpha$, either
there is a homogeneous set of order type $\beta_0$ for color $0$, or there exists some
color $c > 0$ with a homogeneous set of order type $\beta_1$. -/
def OrdinalPartitionMulticolor (α : Ordinal) (k : ℕ) (target₀ target_rest : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < α} → {x : Ordinal // x < α} → Fin (k + 1),
    (∃ g : {x : Ordinal // x < target₀} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < target₀}, i < j → f (g i) (g j) = 0) ∨
    (∃ c : Fin (k + 1), 0 < c.val ∧
      ∃ g : {x : Ordinal // x < target_rest} → {x : Ordinal // x < α},
        StrictMono g ∧
        ∀ i j : {x : Ordinal // x < target_rest}, i < j → f (g i) (g j) = c)

/--
Erdős Problem 1171 [Va99, 7.84]:

Is it true that, for all finite $k < \omega$,
$\omega_1^2 \to (\omega_1 \cdot \omega, 3, \ldots, 3)^2_{k+1}$?

That is, for every $(k+1)$-coloring of pairs of ordinals below $\omega_1^2$, either
there is a homogeneous set of order type $\omega_1 \cdot \omega$ for the first color, or
there is a monochromatic triple for one of the remaining $k$ colors.

Baumgartner [Ba89b] proved that, assuming a form of Martin's axiom,
$\omega_1 \cdot \omega \to (\omega_1 \cdot \omega, 3)^2$.
-/
@[category research open, AMS 3 5]
theorem erdos_1171 : answer(sorry) ↔ ∀ k : ℕ,
    OrdinalPartitionMulticolor (omega1 ^ 2) k (omega1 * omega0) 3 := by
  sorry

end Erdos1171
