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
# Mathoverflow 507128

*Reference:* [mathoverflow/507128](https://mathoverflow.net/questions/507128/embeddability-order-on-picard-groups)
asked by user [*Junyan Xu*](https://mathoverflow.net/users/3332/junyan-xu)
-/

namespace Mathoverflow507128

/-- There exists a proper ideal `I` in a (commutative) total ring `R` of fractions that is an
invertible module. If `I ⊊ R` is such an example, `I` must have infinite order in the Picard group,
and `R` must not be Noetherian (otherwise it must be semi-local and therefore have trivial Picard
group). -/
@[category research open, AMS 13]
theorem exists_isFractionRing_self_ideal_ne_top_invertible :
    ∃ (R : Type) (_ : CommRing R) (_ : IsFractionRing R R) (I : Ideal R),
      I ≠ ⊤ ∧ Module.Invertible R I := by
  sorry

end Mathoverflow507128
