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
# Erdős Problem 1170

*Reference:* [erdosproblems.com/1170](https://www.erdosproblems.com/1170)

Erdős asked whether it is consistent that the ordinal partition relation
$\omega_2 \to (\alpha)^2_2$ holds for every $\alpha < \omega_2$.

- [Va99] Section 7.86.
- [La82] Laver, R., _An (ℵ₂, ℵ₂, ℵ₀)-saturated ideal on ω₁_ (1982), 173–180.
- [FoHa03] Foreman, M. and Hajnal, A., _A partition relation for successors of large cardinals_,
  Math. Ann. (2003), 583–623.

Known partial results:
- [La82] Laver proved the consistency of $\omega_2 \to (\omega_1 \cdot 2 + 1, \alpha)^2$
  for all $\alpha < \omega_2$.
- [FoHa03] Foreman–Hajnal proved the consistency of
  $\omega_2 \to (\omega_1^2 + 1, \alpha)^2$ for all $\alpha < \omega_2$.
-/

open Ordinal Cardinal

namespace Erdos1170

/-- $\omega_2$, the second uncountable ordinal (initial ordinal of cardinality $\aleph_2$). -/
noncomputable def omega2 : Ordinal := (aleph 2).ord

/-- The ordinal partition relation $\kappa \to (\alpha)^2_2$: for every 2-coloring of increasing
pairs of ordinals below $\kappa$, there exists a monochromatic set of order type $\alpha$.
Formalized via strictly monotone embeddings: a subset of order type $\alpha$ corresponds
to a strictly monotone function from $\{x \mid x < \alpha\}$ to $\{x \mid x < \kappa\}$. -/
def OrdinalPartition (κ α : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < κ} → {x : Ordinal // x < κ} → Bool,
    ∃ (c : Bool) (g : {x : Ordinal // x < α} → {x : Ordinal // x < κ}),
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < α}, i < j → f (g i) (g j) = c

/--
Is it consistent that $\omega_2 \to (\alpha)^2_2$ for every $\alpha < \omega_2$?

The arrow notation $\kappa \to (\alpha)^2_2$ denotes the ordinal partition relation: for every
2-coloring of pairs of ordinals below $\kappa$, there exists a monochromatic set of
order type $\alpha$.

This is a consistency question: is there a model of ZFC in which this holds?
We formalize the property itself.

Known partial results:
- Laver [La82] proved the consistency of $\omega_2 \to (\omega_1 \cdot 2 + 1, \alpha)^2$
  for all $\alpha < \omega_2$.
- Foreman–Hajnal [FoHa03] proved the consistency of
  $\omega_2 \to (\omega_1^2 + 1, \alpha)^2$ for all $\alpha < \omega_2$.
-/
@[category research open, AMS 3 5]
theorem erdos_1170 : answer(sorry) ↔
    ∀ α : Ordinal, α < omega2 →
      OrdinalPartition omega2 α := by
  sorry

end Erdos1170
