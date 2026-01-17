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
# Ben Green's Open Problem 47: Inverse large sieve problem

*Reference:*

- [Ben Green's Open Problem 47](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.47)
- B. J. Green and A. Harper, "Inverse questions for the large sieve", Geom. Funct. Anal. Vol.
  24 (2014) 1167–1203
- H. A. Helfgott and A. Venkatesh, "How small must ill-distributed sets be?" Analytic number
  theory, 224–234, Cambridge Univ. Press, Cambridge, 2009.
- M. N. Walsh, "The inverse sieve problem in high dimensions". Duke Math. J. 161 (2012), no.
  10, 2001–2022.
- M. N. Walsh, "The algebraicity of ill-distributed sets". Geom. Funct. Anal. 24 (2014), no. 3,
  959–967.

-/

open Finset

namespace Green47

/--
Suppose that $A \subseteq \mathbf{N}$ satisfies $|A \pmod{p}| \le \frac{p + 1}{2}$ for all
sufficiently large primes $p$. Then either of the conditions are fulfilled:

1. `A` is small in a sense that $|A \cap [1, X]| \ll \frac{X^{1/2}}{(\log X)^{100}}$.

2. `A` is contained in the image of `ℤ` under some quadratic map `φ : ℚ → ℚ`.
--/
@[category research open, AMS 11]
theorem green_47 (A : Finset ℕ) :
    (∀ p : ℕ, 0 < p → (A.image (λ a => a % p)).card ≤ p + 1/2) →
    (∃ C : ℝ, ∀ X : ℕ, #{a ∈ A | a ≤ X} ≤ C * (X : ℝ)^(1/2) / (Real.log X)^100)
    ∨ (∃ a b c : ℚ, ∀ n ∈ A, ∃ z : ℤ, (n : ℚ) = a*z*z + b*z + c) := by
  sorry

end Green47
