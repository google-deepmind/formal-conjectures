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

import FormalConjectures.Util.ProblemImports

open scoped Polynomial

/-
https://mathoverflow.net/questions/339137
asked by user "Sil", https://mathoverflow.net/users/136794/sil

Why do polynomials with coefficients 0,1
 like to have only factors with 0,1
 coefficients?

 Conjecture. Let P(x),Q(x)∈ R[x]
 be two monic polynomials with non-negative coefficients. If R(x)=P(x)Q(x)
 is 0,1 polynomial (coefficients only from {0,1}), then P(x) and Q(x)
 are also 0,1 polynomials.
-/

def IsZeroOne (P : ℝ[X]) := P.coeffs ⊆ {1}

-- TODO(lezeau): add probabilistic reformulation and statament
-- that coefficients must at least lie in `[0, 1]`
@[problem_status open]
theorem mathoverflow_339137 (P Q R : ℝ[X]) (hP: P.Monic) (hQ : Q.Monic)
    (h : R = P * Q) (hR : IsZeroOne R):
    IsZeroOne P ∧ IsZeroOne Q := sorry
