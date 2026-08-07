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
import FormalConjectures.Millenium.PvsNP
import FormalConjecturesForMathlib.Computability.EncodingNat
import Mathlib.Data.Real.Sqrt

/-!
# Integer Factorization in P

This file formally states the conjecture that Integer Factorization is not in P.
It also includes related open complexity problems like Discrete Logarithm and Square-root Sum.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Integer_factorization)
- [Wikipedia](https://en.wikipedia.org/wiki/Discrete_logarithm)
- [Wikipedia](https://en.wikipedia.org/wiki/Square-root_sum_problem)
-/

open Computability ComplexityTheory
open Classical

namespace IntegerFactorization

/--
The decision problem of Integer Factorization:
Given `(N, k)`, does there exist an integer `d` such that `1 < d ≤ k` and `d` divides `N`?
-/
noncomputable def FactorizationDecision (x : ℕ × ℕ) : Bool :=
  if ∃ d, 1 < d ∧ d ≤ x.2 ∧ d ∣ x.1 then true else false

/--
**Integer Factorization is not in P**:

The conjecture that the integer factorization problem is not solvable in deterministic
polynomial time on a classical computer.
-/
@[category research open, AMS 68]
conjecture integer_factorization_not_in_P :
  ¬ IsComputableInPolyTime finEncodingNatProdNat finEncodingBoolBool FactorizationDecision

/--
The decision problem of Discrete Logarithm:
Given `(g, h, p, k)`, does there exist `x ≤ k` such that `g^x ≡ h (mod p)`?
-/
noncomputable def DiscreteLogDecision (input : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let ⟨g, h, p, k⟩ := input
  if ∃ x, x ≤ k ∧ (g ^ x) % p = h % p then true else false

/--
**Discrete Logarithm is not in P**:

The conjecture that the discrete logarithm problem is not solvable in deterministic
polynomial time on a classical computer.
-/
@[category research open, AMS 68]
conjecture discrete_logarithm_not_in_P :
  ¬ IsComputableInPolyTime finEncodingNat4 finEncodingBoolBool DiscreteLogDecision

/--
The decision problem of Square-root Sum:
Given a list of natural numbers `L` and a natural number `k`, is the sum of the square roots
of the elements in `L` less than or equal to `k`?
-/
noncomputable def SquareRootSumDecision (input : List ℕ × ℕ) : Bool :=
  let ⟨L, k⟩ := input
  if (L.map (fun a => Real.sqrt a)).sum ≤ (k : ℝ) then true else false

/--
**Square-root Sum is in P**:

The conjecture that the Square-root Sum problem is solvable in deterministic
polynomial time on a classical computer. (This is a major open problem in numerical geometry).
-/
@[category research open, AMS 68]
conjecture square_root_sum_in_P :
  IsComputableInPolyTime finEncodingListNatProdNat finEncodingBoolBool SquareRootSumDecision

end IntegerFactorization
