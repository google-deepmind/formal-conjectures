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
# The irrationality exponent of the natural logarithm of 2

Determine the irrationality exponent of $\log 2$, where $\log$ is the natural
logarithm. Bugeaud and Kim [BK26, Section 1] record its exact value as unknown.
The statement below gives the value $2$, with a Lean formalization by
Kenta Kitamura [Ki26].

*References:*
- [BK26] Y. Bugeaud and D. H. Kim, *On the b-ary expansion of a real number whose
  irrationality exponent is close to 2*,
  [arXiv:2510.02059v2](https://arxiv.org/abs/2510.02059v2) (2026),
  Section 1, Definition 1.1 and the discussion of classical constants.
- [Ki26] Kenta Kitamura, *log2-irrationality-exponent*, Lean 4 formalization (2026),
  [GitHub repository](https://github.com/KitaKen1/log2-irrationality-exponent/tree/93a66a6c6b69e5e2f7775d791fd4943f4b1cf671).
-/

@[expose] public section

namespace LogTwo

/-- The supremum of positive $\mu$ for which infinitely many reduced rationals
$p/q$, with $q > 1$, satisfy $0 < |x-p/q| < 1/q^\mu$.
This real-valued definition represents the irrationality exponent when the
set of such exponents is nonempty and bounded above. -/
noncomputable def irrationalityExponent (x : ℝ) : ℝ :=
  sSup {μ : ℝ | 0 < μ ∧ Set.Infinite
    {r : ℚ | 1 < r.den ∧ 0 < |x - (r : ℝ)| ∧
      |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}}

/-- What is the irrationality exponent of the natural logarithm of $2$?
Its exact value is listed as unknown in [BK26, Section 1]. The answer is $2$ [Ki26]. -/
@[category research solved, AMS 11,
    formal_proof using lean4 at "https://github.com/KitaKen1/log2-irrationality-exponent/blob/93a66a6c6b69e5e2f7775d791fd4943f4b1cf671/lean/LogTwo/Target.lean#L45-L48"]
theorem irrationalityExponent_log_two :
    irrationalityExponent (Real.log 2) = answer(2) := by
  sorry

end LogTwo
