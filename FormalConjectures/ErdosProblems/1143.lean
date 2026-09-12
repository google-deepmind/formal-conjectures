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
# Erdős Problem 1143

*References:*
- [erdosproblems.com/1143](https://www.erdosproblems.com/1143)
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
-/

open Finset

namespace Erdos1143

/--
The number of integers in the half-open interval $[n, n+k)$ that are divisible by at least one
element of `P`.
-/
def multiplesInInterval (P : Finset ℕ) (n k : ℕ) : ℕ :=
  ((Ico n (n + k)).filter fun m => ∃ p ∈ P, p ∣ m).card

/--
$F_k(p_1,\ldots,p_u)$ is the largest integer such that every interval of $k$ consecutive positive
integers contains at least that many multiples of at least one of the $p_i$. Equivalently, it is
the minimum of that count over all such intervals.

The primes are packaged as a finite set `P`; the problem's $p_u$ is then `P.max'`.
-/
noncomputable def F (k : ℕ) (P : Finset ℕ) : ℕ :=
  sInf (Set.range fun n : ℕ => multiplesInInterval P (n + 1) k)

/-- `F k P` is a lower bound for the count in every interval of length `k`. -/
@[category API, AMS 11]
theorem F_le_multiplesInInterval (k n : ℕ) (P : Finset ℕ) :
    F k P ≤ multiplesInInterval P (n + 1) k :=
  Nat.sInf_le (Set.mem_range_self n)

/-- The empty set of primes contributes no multiples, so $F_k(\emptyset)=0$. -/
@[category test, AMS 11]
theorem F_empty (k : ℕ) : F k ∅ = 0 := by
  simp [F, multiplesInInterval]

/-- Among two consecutive positive integers starting at $1$, exactly one is even. -/
@[category test, AMS 11]
theorem multiplesInInterval_two_evens : multiplesInInterval {2} 1 2 = 1 := by
  decide

/-- A singleton interval starting at an odd integer contains no multiple of $2$. -/
@[category test, AMS 11]
theorem multiplesInInterval_one_odd : multiplesInInterval {2} 1 1 = 0 := by
  decide

/--
Let $p_1<\cdots<p_u$ be primes and let $k\geq 1$. Let $F_k(p_1,\ldots,p_u)$ be such that every interval of $k$ positive integers contains at least $F_k(p_1,\ldots,p_u)$ multiples of at least one of the $p_i$.

Estimate $F_k(p_1,\ldots,p_u)$, particularly in the range $k=\alpha p_u$ for constant $\alpha>2$.

In \cite{Va99} it is reported that Erdős and Selfridge found 'the exact bound' when $2<\alpha<3$, and that 'if $\alpha>3$ then very little is known'. No reference is given, and I cannot find a relevant paper of Erdős and Selfridge.

See also [970](https://www.erdosproblems.com/970).
-/
@[category research open, AMS 11]
theorem erdos_1143 :
    let ans : ℝ → Finset ℕ → ℕ := answer(sorry)
    ∀ α : ℝ, 2 < α → ∀ P : Finset ℕ, (hP : P.Nonempty) →
      (∀ p ∈ P, p.Prime) →
        F ⌊α * (P.max' hP : ℝ)⌋₊ P = ans α P := by
  sorry

end Erdos1143
