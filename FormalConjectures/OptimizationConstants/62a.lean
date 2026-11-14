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
module

public import FormalConjecturesUtil

/-!
# Lindelof (pointwise growth) exponent for the Riemann zeta function C62a
*Reference:*
- [Lindelof (pointwise growth) exponent for the Riemann zeta function](https://teorth.github.io/optimizationproblems/constants/62a.html)
- [Bou2017] Bourgain, Jean. "Decoupling, exponential sums and the Riemann zeta function."
  Journal of the American Mathematical Society 30 (2017), no. 1, 205-224. (https://arxiv.org/pdf/1408.5794.pdf)
- [Har2019] Harper, Adam. "La fonction zeta de Riemann dans les petits intervalles."
  Seminaire Bourbaki, Expose 1159 (2017/2018), Asterisque 414 (2019), 429-464. (https://www.bourbaki.fr/TEXTES/Exp1159-Harper.pdf)
-/

@[expose] public section

open Set Complex Asymptotics Filter

namespace Constant62a

/-- **Lindelof (pointwise growth) exponent for the Riemann zeta function**:
The constant is given by $C_{62a} = \inf \{ \theta \geq 0 : | \zeta (1/2 + it) |
\ll_{\varepsilon} (1 + |t|)^{\theta + \varepsilon} \textnormal{ for all } \varepsilon > 0 \}$.
-/
@[optimization_constant "62a"]
noncomputable def C62a : ℝ :=
  sInf {C : ℝ | C ≥ 0 ∧ ∀ (ε : ℝ), ε > 0 → ((fun (t : ℝ) => ‖riemannZeta (1 / 2 + I * t)‖)
  =O[cocompact ℝ] (fun (t : ℝ) => (1 + ‖t‖) ^ (C + ε)))}

/-- The Lindelöf hypothesis: $C_{62a} = 0$ [Har2019].
-/
@[category research open, AMS 32]
theorem lindelof_hypothesis : C62a = 0 := by
  sorry

/-- The proven convexity upper bound: $C_{62a} \leq 1/4$ [Har2019].
-/
@[category research solved, AMS 32]
theorem c62a_upperbound_convexity : C62a ≤ 1 / 4 := by
  sorry

/-- The proven Hardy-Littlewood upper bound: $C_{62a} \leq 1/6$ [Har2019].
-/
@[category research solved, AMS 32]
theorem c62a_upperbound_hardy_littlewood : C62a ≤ 1 / 6 := by
  sorry

/-- The proven Bourgain's pointwise upper bound: $C_{62a} \leq 13/84$ [Bou2017].
-/
@[category research solved, AMS 32]
theorem c62a_upperbound_bourgain : C62a ≤ 13 / 84 := by
  sorry

/-- The trivial (best known) lower bound: $C_{62a} \geq 0$.
-/
@[category textbook, AMS 32]
lemma c62a_lower_bound : C62a ≥ 0 := by
  sorry

end Constant62a
