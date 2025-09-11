/-
Copyright 2025 Google LLC

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

-- https://en.wikipedia.org/wiki/Irrational_number#Open_questions
import FormalConjectures.Util.ProblemImports

open Real
open Finset

local notation "e" => exp 1

/-- $e + \pi$ is irrational -/
@[open_problem]
theorem irrational_e_plus_pi : Irrational (e + π) := sorry

/-- $e \pi$ is irrational -/
@[open_problem]
theorem irrational_e_times_pi : Irrational (e * π) := sorry

/-- $e ^ e$ is irrational -/
@[open_problem]
theorem irrational_e_to_e : Irrational (e ^ e) := sorry

/-- $\pi ^ e$ is irrational -/
@[open_problem]
theorem irrational_pi_to_e : Irrational (π ^ e) := sorry

/-- $\pi ^ \pi$ is irrational -/
@[open_problem]
theorem irrational_pi_to_pi : Irrational (π ^ π) := sorry

/-- $\ln(\pi)$ is irrational -/
@[open_problem]
theorem irrational_ln_pi : Irrational (log π) := sorry

/-- The the difference between harmonic series and natural logarithm, also known
as Euler-Mascheroni constant $\gamma$ is irrational -/
@[open_problem]
theorem irrational_euler_mascheroni :
    Irrational eulerMascheroniConstant := sorry

/-- $\zeta(5)$ is irrational where $\zeta$ is the Riemann zeta function. -/
@[open_problem]
theorem irrational_zeta_5 : Irrational (riemannZeta 5).re := sorry

/-- $\zeta(7)$ is irrational where $\zeta$ is the Riemann zeta function. -/
@[open_problem]
theorem irrational_zeta_7 : Irrational (riemannZeta 7).re := sorry

/-- $\zeta(9)$ is irrational where $\zeta$ is the Riemann zeta function. -/
@[open_problem]
theorem irrational_zeta_9 : Irrational (riemannZeta 9).re := sorry

/-- $\zeta(n)$ is irrational for all odd $n > 3$,
where $\zeta$ is the Riemann zeta function. -/
@[open_problem]
theorem irrational_zeta_all_odd :
    ∀ n : ℕ, Irrational (riemannZeta (2*n+5)).re := sorry

/-- The Catalan constant is irrational -/
@[open_problem]
theorem irrational_catalan_constant :
    Irrational (∑' n : ℕ, (-1)^n / (2*n + 1)^2 ) := sorry
