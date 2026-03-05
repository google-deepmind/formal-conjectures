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
# Erdős Problem 514

Does every entire transcendental function admit a continuous path going to infinity along which
the function grows faster than any polynomial? A related question asks whether the growth rate
along such a path can be estimated in terms of the maximum modulus.

*Reference:* [erdosproblems.com/514](https://www.erdosproblems.com/514)
-/

open Complex Filter Topology

namespace Erdos514

/-- The maximum modulus of $f$ on the circle of radius $r$:
$M(r) = \sup \{ \|f(z)\| \mid \|z\| = r \}$. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- Erdős Problem 514 (proved by Boas, unpublished):
For every entire transcendental function $f$, there exists a continuous path $\gamma$
going to infinity such that $|f(\gamma(t))/\gamma(t)^n| \to \infty$ for every $n$. -/
@[category research solved, AMS 30]
theorem erdos_514 :
    ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) →
      ∃ γ : ℝ → ℂ, Continuous γ ∧
        Tendsto (fun t => ‖γ t‖) atTop atTop ∧
        ∀ n : ℕ, Tendsto (fun t => ‖f (γ t)‖ / ‖γ t‖ ^ n) atTop atTop := by
  sorry

/-- Erdős Problem 514, growth rate variant (open):
For every entire transcendental function $f$ and every $\varepsilon > 0$, does there exist a
continuous path $\gamma$ going to infinity along which $|f(z)| \geq M(|z|)^\varepsilon$? -/
@[category research open, AMS 30]
theorem erdos_514.variants.max_modulus_growth :
    answer(sorry) ↔
      ∀ f : ℂ → ℂ, Differentiable ℂ f →
        (¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) →
        ∀ ε : ℝ, 0 < ε →
          ∃ γ : ℝ → ℂ, Continuous γ ∧
            Tendsto (fun t => ‖γ t‖) atTop atTop ∧
            ∀ᶠ t in atTop, (maxModulus f ‖γ t‖) ^ ε ≤ ‖f (γ t)‖ := by
  sorry

end Erdos514
