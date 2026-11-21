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
# Erdős Problem 684

*References:*
- [erdosproblems.com/684](https://www.erdosproblems.com/684)
- [APSSV26] Alexeev, B., Putterman, M., Sawhney, M., Sellke, M., and Valiant, G.,
  *Short proofs in combinatorics and number theory*. arXiv:2603.29961 (2026), Theorem 2.1.
-/

@[expose] public section

namespace Erdos684

open Filter Real

/-- The factor of $\binom{n}{k}$ containing the full multiplicity of every prime at most $k$. -/
def smallPrimePart (n k : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE k, p ^ ((n.choose k).factorization p)

@[category test, AMS 11]
theorem smallPrimePart_zero (n : ℕ) : smallPrimePart n 0 = 1 := by
  simp [smallPrimePart]

set_option linter.style.formal_proof_palomar false in
/-- Let $f(n)$ be the smallest $0 \leq k \leq n$ for which the factor of
$\binom{n}{k}$ supported on primes at most $k$ exceeds $n^2$. Give bounds for $f(n)$.

An internal OpenAI model [APSSV26] has given an elementary argument which shows
$f(n) \ll (\log n)^2$. This statement gives the nonoptimal constant $514$.
The existence formulation avoids defining the minimum for small inputs. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Solution.lean"]
theorem erdos_684.upper_bound :
    ∀ᶠ n : ℕ in atTop, ∃ k ≤ n,
      (k : ℝ) ≤ 514 * (log (n : ℝ)) ^ 2 ∧ n ^ 2 < smallPrimePart n k := by
  sorry

set_option linter.style.formal_proof_palomar false in
/-- The elementary argument of an internal OpenAI model [APSSV26] constructs arbitrarily
large $n$ such that $f(n) \geq (1/2-o(1))\log n$. The following weaker form has coefficient
$1/8$: for arbitrarily large $n>1$, the small-prime part equals one for every
$k \leq (\log n)/8$. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Lower.lean"]
theorem erdos_684.lower_bound :
    ∃ᶠ n : ℕ in atTop, 1 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ log (n : ℝ) / 8 → smallPrimePart n k = 1 := by
  sorry

end Erdos684

