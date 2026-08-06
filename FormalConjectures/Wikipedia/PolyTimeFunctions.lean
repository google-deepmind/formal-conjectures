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
import FormalConjecturesUtil

/-!
# Polynomial-time computable functions

This file contains formal statements of some open problems
related to polynomial-time computable functions with a number theoretical flavor.

These statements are phrased using `ComplexityTheory.IsPolyTime`
(defined in `FormalConjecturesForMathlib.Computability.ComplexityTheory`),
which assumes the presence of a canonical `BitstringEncoding`
for the domain and codomain of the function in question.

## Main Statements

The following statements represent open questions of polynomial-time computability:

* `isPolyTime_primeFactorsList` — integer factorization is in P.
* `isPolyTime_discreteLog` — the discrete logarithm is in P.
* `isPolyTime_sqrtSumLE` — square-root-sum is in P.

We also include a formalization of the known but nontrivial result
that primality testing is in P:

* `isPolyTime_primeDecision` — primality testing is in P (AKS, 2002).

*References:*
- [Wikipedia, List of unsolved problems in computer science](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_computer_science)

-/

namespace PolyTime

open ComplexityTheory

/--
**Is integer factorization computable in polynomial time?**

`Nat.primeFactorsList` maps a natural number to its sorted list of prime factors, so this
asks whether there is a polynomial-time algorithm producing the full factorization.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Integer_factorization) -/
@[category research open, AMS 68]
theorem isPolyTime_primeFactorsList : answer(sorry) ↔ IsPolyTime Nat.primeFactorsList := by
  sorry

/-- The discrete logarithm: the least `x < p` with `g ^ x ≡ h [MOD p]`, or `0` if none
exists. -/
def discreteLog (p g h : ℕ) : ℕ :=
  if hx : ∃ x, x < p ∧ g ^ x % p = h % p then Nat.find hx else 0

/--
**Is the discrete logarithm in ℤ_p computable in polynomial time?**

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Discrete_logarithm)
-/
@[category research open, AMS 68]
theorem isPolyTime_discreteLog :
    answer(sorry) ↔ IsPolyTime fun x : ℕ × ℕ × ℕ => discreteLog x.1 x.2.1 x.2.2 := by
  sorry

open Classical in
/-- The square-root-sum comparison: given lists `a b` of naturals, decides whether
`∑ i ∈ a, √i ≤ ∑ j ∈ b, √j`. -/
noncomputable def sqrtSumLE (a b : List ℕ) : Bool :=
  decide ((a.map fun n => Real.sqrt n).sum ≤ (b.map fun n => Real.sqrt n).sum)

/-- **Is square-root-sum in P?**

Comparing sums of square roots is a famous problem (Garey–Graham–Johnson 1976) not even
known to lie in NP; the difficulty is bounding the precision needed to separate the two
sums.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Square-root_sum_problem) -/
@[category research open, AMS 68]
theorem isPolyTime_sqrtSumLE :
    answer(sorry) ↔ IsPolyTime fun x : List ℕ × List ℕ => sqrtSumLE x.1 x.2 := by
  sorry

/- ## Problems that turned out to be in P

For contrast with the open conjectures above, here is a classical
problem whose membership in P was once unclear but is now a *theorem*. This challenge
is honest: a proof "only" requires formalizing the corresponding algorithm and its
runtime analysis. -/

/-- The primality decision function. -/
def primeDecision (n : ℕ) : Bool :=
  decide n.Prime

/-- **Primality testing is in P.**

This is "PRIMES is in P", proved by Agrawal–Kayal–Saxena (2002). Before AKS,
primality was a canonical candidate for a problem in NP ∩ co-NP but not P.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/AKS_primality_test) -/
@[category research solved, AMS 68]
theorem isPolyTime_primeDecision : IsPolyTime primeDecision := by
  sorry

end PolyTime
