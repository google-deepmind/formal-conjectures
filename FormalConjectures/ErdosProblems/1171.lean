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
-/

open Cardinal Ordinal SimpleGraph

namespace Erdos1171

/--
**Erdős Problem 1171.** Is it true that for all finite $k < \omega$,
$$\omega_1^2 \to (\omega_1 \cdot \omega, \underbrace{3, \ldots, 3}_{k})^2_{k+1}?$$

In any $(k+1)$-coloring of the pairs of the complete graph on $\omega_1^2$, either
there is a color-0 set of order type $\omega_1 \cdot \omega$, or there is a
monochromatic triangle $K_3$ in some non-zero color. The case $k = 1$
(`erdos_1171.variants.k_one`) is the Erdős–Hajnal theorem [EH74].
-/
@[category research open, AMS 5]
theorem erdos_1171 :
    answer(sorry) ↔
      ∀ k : ℕ, OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k := by
  sorry

namespace erdos_1171.variants

/--
**Erdős–Hajnal theorem** [EH74]: the case $k = 1$,
$\omega_1^2 \to (\omega_1 \cdot \omega, 3)^2$.
-/
@[category research solved, AMS 5]
theorem k_one : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 1 := by
  sorry

/--
`OrdinalMultiColorRamsey` is monotone in the number of non-zero colors:
a witness for the `k`-color version yields one for any `j ≤ k`.
-/
@[category API, AMS 5]
theorem mono_k {j k : ℕ} (hjk : j ≤ k)
    (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  sorry

/- **Baumgartner under MA (currently deferred)** [Ba89b]: assuming a form of Martin's
Axiom, the binary partition relation `ω₁·ω → (ω₁·ω, 3)²` holds. We omit the Lean
statement for now because faithfully encoding the exact form of MA requires more work;
stating the result as `True → ...` would effectively make it unconditional. To be
restored once an appropriate MA predicate is available in the formalization. -/

end erdos_1171.variants

end Erdos1171
