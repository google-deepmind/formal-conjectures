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

import FormalConjecturesUtil
/-!
# Mathoverflow 507128

*Reference:* [mathoverflow/507128](https://mathoverflow.net/questions/507128/embeddability-order-on-picard-groups)
asked by user [*Junyan Xu*](https://mathoverflow.net/users/3332/junyan-xu)
-/

namespace Mathoverflow507128

/-- There exists a proper ideal `I` in a (commutative) total ring `R` of fractions that is an invertible module.
If `I ⊊ R` is such an example, `I` must have infinite order in the Picard group.
Moreover, `R` must not be Noetherian (otherwise it must be semi-local and therefore have trivial Picard group).

The linked formal proof gives the following explicit construction.

Let `D = ℂ[X, Y] / (Y² - X³)` be the coordinate ring of the cuspidal cubic.
Let `P = (X - 1, Y - 1)`, which is an invertible ideal.
Let `M` be the direct sum of the evaluation fibres at cusp parameters `r ≠ 1`.
Form the idealization `R = D ⋉ M`.
The desired ideal is the range of the multiplication map `R ⊗[D] P → R`.
-/
@[category research solved, AMS 13,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/mo507128-lean/commit/e9507429c01c4288089e4af1c92a03b7d1e17f74"]
theorem exists_isFractionRing_self_ideal_ne_top_invertible :
    ∃ (R : Type) (_ : CommRing R) (_ : IsFractionRing R R) (I : Ideal R),
      I ≠ ⊤ ∧ Module.Invertible R I := by
  sorry

end Mathoverflow507128
