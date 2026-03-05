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
# Erdős Problem 1172

*Reference:* [erdosproblems.com/1172](https://www.erdosproblems.com/1172)

Establish whether certain ordinal partition relations hold under the Generalized Continuum
Hypothesis or the Continuum Hypothesis. A problem of Erdős and Hajnal.

[Va99] Hajnal, A. and Larson, J., *Partition relations*. Handbook of Set Theory (2010).
-/

open Ordinal Cardinal

namespace Erdos1172

/-- $\omega$, the first infinite ordinal. -/
noncomputable def omega0 : Ordinal := (aleph 0).ord

/-- $\omega_1$, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- $\omega_2$, the second uncountable ordinal. -/
noncomputable def omega2 : Ordinal := (aleph 2).ord

/-- $\omega_3$, the third uncountable ordinal. -/
noncomputable def omega3 : Ordinal := (aleph 3).ord

/-- The ordinal partition relation $\alpha \to (\beta, \gamma)^2$ for 2-colorings of pairs.
    For every 2-coloring of the pairs of ordinals below $\alpha$, there is either
    a homogeneous set of order type $\beta$ in color true, or a homogeneous set of
    order type $\gamma$ in color false. Formalized via strictly monotone embeddings:
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

/-- The Generalized Continuum Hypothesis: $2^{\aleph_o} = \aleph_{o+1}$ for all ordinals $o$. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ aleph o = aleph (o + 1)

/-- The Continuum Hypothesis: $2^{\aleph_0} = \aleph_1$. -/
def CH : Prop := (2 : Cardinal.{0}) ^ aleph 0 = aleph 1

/--
Erdős Problem 1172, Part 1 [Va99, 7.87]:

Assuming the Generalized Continuum Hypothesis, establish whether
$$\omega_3 \to (\omega_2, \omega_1 + 2)^2.$$

This is an open problem of Erdős and Hajnal. The right-hand side may have
been filled in incorrectly due to a truncated photocopy of the source [Va99].
-/
@[category research open, AMS 3 5]
theorem erdos_1172 : answer(sorry) ↔ (GCH →
    OrdinalPartitionPair omega3 omega2 (omega1 + 2)) := by
  sorry

/--
Erdős Problem 1172, Part 2 [Va99, 7.87]:

Assuming the Generalized Continuum Hypothesis, establish whether
$$\omega_3 \to (\omega_2 + \omega_1, \omega_2 + \omega)^2.$$

This is an open problem of Erdős and Hajnal.
-/
@[category research open, AMS 3 5]
theorem erdos_1172.variants.gch_partition_2 : answer(sorry) ↔ (GCH →
    OrdinalPartitionPair omega3 (omega2 + omega1) (omega2 + omega0)) := by
  sorry

/--
Erdős Problem 1172, Part 3 [Va99, 7.87]:

Assuming the Generalized Continuum Hypothesis, establish whether
$$\omega_2 \to (\omega_1^{\omega+2} + 2, \omega_1 + 2)^2.$$

This is an open problem of Erdős and Hajnal. The right-hand side may have
been filled in incorrectly due to a truncated photocopy of the source [Va99].
-/
@[category research open, AMS 3 5]
theorem erdos_1172.variants.gch_partition_3 : answer(sorry) ↔ (GCH →
    OrdinalPartitionPair omega2 (omega1 ^ (omega0 + 2) + 2) (omega1 + 2)) := by
  sorry

/--
Erdős Problem 1172, Part 4 [Va99, 7.87]:

Assuming the Continuum Hypothesis, establish whether
$$\omega_2 \to (\omega_1 + \omega)^2_2.$$

That is, for every 2-coloring of the pairs of ordinals below $\omega_2$, there exists
a monochromatic homogeneous set of order type $\omega_1 + \omega$.

This is an open problem of Erdős and Hajnal.
-/
@[category research open, AMS 3 5]
theorem erdos_1172.variants.ch_partition : answer(sorry) ↔ (CH →
    OrdinalPartitionPair omega2 (omega1 + omega0) (omega1 + omega0)) := by
  sorry

end Erdos1172
