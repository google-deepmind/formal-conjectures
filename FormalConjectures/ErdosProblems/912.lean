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
# Erdős Problem 912

*References:*
 - [erdosproblems.com/912](https://www.erdosproblems.com/912)
 - [Er82c] Erdős, P., Miscellaneous problems in number theory. Congr. Numer. (1982), 25-45.
-/

open scoped Nat Asymptotics
open Filter

namespace Erdos912

/-- If $n! = \prod_{i}p_i^{k_i}$ is the factorization into distinct primes, then we define $h(n)$
to be the number of distinct exponents $k_i$. -/
noncomputable def h (n : ℕ) : ℕ := (n !).factorization.frange.card

/-- Erdős and Selfridge prove in [Er82c] that $h(n) \asymp \left(\frac{n}{\log n}\right)^{1/2}$. -/
@[category research solved, AMS 11]
theorem erdos_912.variants.selfridge :
    (fun n => (h n : ℝ)) =Θ[atTop] (fun n => (n / Real.log n) ^ (1 / 2 : ℝ)) := by
  sorry

/-- Prove that there exists some $c>0$ such that
$$h(n) \sim c \left(\frac{n}{\log n}\right)^{1/2}$$
as $n\to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_912 : ∃ c > 0,
    (fun n => (h n : ℝ)) ~[atTop] (fun n => c * (n / Real.log n) ^ (1 / 2 : ℝ)) := by
  sorry

/-- A heuristic of Tao using the Cramér model for the primes suggests this is true with
$c=\sqrt{2\pi}$. -/
@[category research open, AMS 11]
theorem erdos_912.variants.tao :
    (fun n => (h n : ℝ)) ~[atTop] (fun n => √(2 * Real.pi) * (n / Real.log n) ^ (1 / 2 : ℝ)) := by
  sorry

end Erdos912
