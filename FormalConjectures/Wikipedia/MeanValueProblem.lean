/-
Copyright 2025 The Formal Conjectures Authors.

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
# Mean value problem

*Reference:*
- [Wikipedia](https://en.wikipedia.org/wiki/Mean_value_problem)
- [The fundamental theorem of algebra and complexity theory](https://www.ams.org/journals/bull/1981-04-01/S0273-0979-1981-14858-8/)
by Steve Smale

Given a complex polynomial $p$ of degree $d ≥ 2$ and a complex number $z$
there is a critical point $c$ of $p$, such that $|p(z)-p(c)|/|z-c| ≤ K* |p'(z)|$ for $K=1$.


The conjecture has been proven for:
* `K = 4`
  [The fundamental theorem of algebra and complexity theory](https://www.ams.org/journals/bull/1981-04-01/S0273-0979-1981-14858-8/)
  by *Steve Smale*
* `K = (d-1)/d` if $p$ has real roots or all the roots of $p$ have the same norm.
  [Critical points and values of complex polynomials](https://doi.org/10.1016/0885-064X(89)90019-8)
  by *David Tischler*
-/

/--
Given a complex polynomial $p$ of degree $d ≥ 2$ and a complex number $z$
there is a critical point $c$ of $p$, such that $|p(z)-p(c)|/|z-c| ≤ |p'(z)|$.
-/
@[category research open, AMS 12]
lemma mean_value_problem (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ):
    ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ ‖p.derivative.eval z‖ :=
  sorry

/--
The following weaker version of the mean value problem has been proven.
Given a complex polynomial $p$ of degree $d ≥ 2$ and a complex number $z$
there a critical point $c$ of $p$, such that $|p(z)-p(c)|/|z-c| ≤ 4|p'(z)|$.
-/
@[category research solved, AMS 12]
lemma mean_value_problem_leq_4 (p : Polynomial ℂ) (hp : 2 ≤ p.degree) (z : ℂ) (K : ℝ):
    ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ 4 *‖p.derivative.eval z‖ :=
  sorry

/--
The following tighter bound depending on the degree $d$ of the polynomial $p$,
in the case of $p$ only having real roots has been shown by Tischler.
|p(z)-p(c)|/|z-c| ≤ (d-1)/d * |p'(z)|
-/

@[category research solved, AMS 12]
lemma mean_value_problem_of_real_roots (p : Polynomial ℂ) (hp : 2 ≤ p.natDegree)
    (h : ∀ x : ℂ, p.IsRoot x → x.im = 0) (z : ℂ) (K : ℝ) :
    ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ (p.natDegree - 1)/ p.natDegree * ‖p.derivative.eval z‖ :=
  sorry

/--
The following tighter bound depending on the degree $d$ of the polynomial $p$,
in the case of $p$ all roots having the same norm has been shown by Tischler.
|p(z)-p(c)|/|z-c| ≤ (d-1)/d * |p'(z)|
-/

@[category research solved, AMS 12]
lemma mean_value_problem_of_roots_same_norm (p : Polynomial ℂ) (hp : 2 ≤ p.natDegree)
    (h : ∀ x  y : ℂ, p.IsRoot x ∧ p.IsRoot y → ‖x‖=‖y‖) (z : ℂ) (K : ℝ) :
    ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ (p.natDegree - 1)/ p.natDegree * ‖p.derivative.eval z‖ :=
  sorry
