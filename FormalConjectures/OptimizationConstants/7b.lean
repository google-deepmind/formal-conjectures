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
import FormalConjectures.OptimizationConstants.«7a»
import FormalConjecturesUtil

/-!
# Tao's Optimization Constant 7b / The Irrationality Measure of $\Gamma(1/4)$

*References:*
- [Tao's Optimization Constant 7b](https://teorth.github.io/optimizationproblems/constants/7b.html)
- [D1842] Dirichlet, L. G. P., *Verallgemeinerung eines Satzes aus der Lehre von den
  Kettenbrüchen nebst einigen Anwendungen auf die Theorie der Zahlen*. Sitzungsberichte der
  Preussischen Akademie der Wissenschaften (1842), 93–95.
- [C1976] Chudnovsky, G. V., *Algebraic independence of constants connected with the exponential
  and the elliptic functions*. Dokl. Akad. Nauk Ukrain. SSR Ser. A 1976, no. 8, 698–701.
- [Bru2002] Bruiltet, S., [*D'une mesure d'approximation simultanée à une mesure
  d'irrationalité :
  le cas de $\Gamma(1/4)$ et $\Gamma(1/3)$*](https://doi.org/10.4064/aa104-3-3).
  Acta Arith. **104** (2002), 243–281.
-/

namespace Constant7b

open ENNReal

/-- **Tao's Optimization Constant 7b / The irrationality measure of $\Gamma(1/4)$**. -/
noncomputable def C7b : ℝ≥0∞ :=
  Constant7a.irrationalityExponent (Real.Gamma (1 / 4))

/-- $\Gamma(1/4)$ is irrational, as proven in [C1976]. -/
@[category research solved, AMS 11 33]
theorem irrational_gamma_one_div_four : Irrational (Real.Gamma (1 / 4)) := by
  sorry

/-- The first and current best known lower bound, given by Dirichlet's theorem [D1842]. It applies
because $\Gamma(1/4)$ is irrational by Chudnovsky's theorem [C1976]. -/
@[category research solved, AMS 11 33]
theorem c7b_lower_bound : 2 ≤ C7b :=
  Constant7a.two_le_irrationalityExponent irrational_gamma_one_div_four

/-- Can the current best lower bound be improved? -/
@[category research open, AMS 11 33]
theorem c7b_lower_bound_improved : answer(sorry) ↔ 2 < C7b := by
  sorry

/-- The first and current best known upper bound, proved by Bruiltet in [Bru2002]. It follows from
an explicit lower bound on $|\Gamma(1/4) - p/q|$ for rational $p/q$ of sufficiently large height. -/
@[category research solved, AMS 11 33]
theorem c7b_upper_bound : C7b ≤ 10 ^ 143 := by
  sorry

/-- Can the current best upper bound be improved? -/
@[category research open, AMS 11 33]
theorem c7b_upper_bound_improved : answer(sorry) ↔ C7b < 10 ^ 143 := by
  sorry

end Constant7b
