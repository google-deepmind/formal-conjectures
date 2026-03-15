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

Hajnal proved this holds assuming the Continuum Hypothesis. The problem is
independent of ZFC: it is consistent with ZFC but not provable from ZFC alone.

See also Problem 592 (a related question concerning countable ordinals)
and Problem 1172 (which uses the same `OrdinalPartitionPair` definition).

*Reference:* [erdosproblems.com/1169](https://www.erdosproblems.com/1169)

[Va99] Hajnal, A. and Larson, J., _Partition relations_. Handbook of Set Theory (2010), §7.85.

[Ha71] Hajnal, A., _A negative partition relation_. Proceedings of the National Academy of
  Sciences U.S.A. (1971), 142–144.
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
Erdős Problem #1169 [Va99, 7.85] (Erdős and Hajnal):

Is it true that, for all finite $k \geq 3$,
$$\omega_1^2 \not\to (\omega_1^2, k)^2?$$

That is, for every natural number $k \geq 3$, there exists a 2-coloring of the pairs
of ordinals below $\omega_1^2$ such that no subset of order type $\omega_1^2$ is monochromatic
in the first color and no subset of order type $k$ is monochromatic in the
second color.

Hajnal proved this holds assuming the Continuum Hypothesis [Ha71].
The problem is independent of ZFC: consistent with ZFC but not provable
from ZFC alone.

The restriction to $k \geq 3$ is necessary because the partition relation
$\omega_1^2 \to (\omega_1^2, k)^2$ holds trivially for $k \leq 2$.
-/
@[category research open, AMS 3 5]
theorem erdos_1169 : answer(sorry) ↔
    ∀ k : ℕ, 3 ≤ k → ¬ OrdinalPartitionPair (omega1 ^ 2) (omega1 ^ 2) (↑k) := by
  sorry

end Erdos1169
