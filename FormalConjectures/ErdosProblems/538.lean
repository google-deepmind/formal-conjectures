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

import FormalConjecturesUtil

/-!
# Erdős Problem 538

*Reference:* [erdosproblems.com/538](https://www.erdosproblems.com/538)
-/

namespace Erdos538

open scoped Classical

/-- The representations `m = p * a` with `p` prime and `a ∈ A`. -/
def representations (A : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ A).filter (fun pa => Nat.Prime pa.1 ∧ m = pa.1 * pa.2)

/-- `A ⊆ {1, …, N}` and every `m` has at most `r` representations `m = p a`. -/
def Admissible (r N : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ ∀ m : ℕ, (representations A m).card ≤ r

/-- The reciprocal sum `∑_{n ∈ A} 1/n` of the problem. -/
def reciprocalMass (A : Finset ℕ) : ℚ := ∑ a ∈ A, (1 : ℚ) / a

/--
Let $r\geq 2$ and suppose that $A\subseteq\{1,\ldots,N\}$ is such that, for any
$m$, there are at most $r$ solutions to $m=pa$ where $p$ is prime and $a\in A$.
Give the best possible upper bound for $\sum_{n\in A}\frac{1}{n}$.

The reciprocal sum has matching order $\Theta_r(\log N / \log\log N)$: an
explicit two-sided bound (upper for every admissible `A`, together with a
witnessing construction) pins the order, up to the one iterated-logarithm factor.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/main/starfleet/erdos-538/Research/FinalMatchingOrder.lean"]
theorem erdos_538 (r N : ℕ) (hr : 2 ≤ r) (hN : 2 ≤ N) :
    (∀ A : Finset ℕ, Admissible r N A →
      Real.log (Real.log (N + 1)) * (reciprocalMass A : ℝ) ≤
        2 * r * (1 + Real.log (N * N))) ∧
    (∃ A : Finset ℕ, Admissible r N A ∧
      Real.log (N + 1) ≤
        4 + (8192 * (Nat.log 2 (Nat.log 2 N) + 1) : ℝ) * (reciprocalMass A : ℝ)) := by
  sorry

end Erdos538
