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
# Idoneal numbers completeness conjecture

An integer $D>0$ is **idoneal** if every
integer that can be expressed in exactly one way (up to order and signs)
as $x^2 + D y^2$ with gcd(x, Dy)=1 is a prime power or twice a prime power.

The Idoneal Numbers Completeness Conjecture asserts that the following list of
65 numbers is complete:
1,2,3,4,5,6,7,8,9,10,12,13,15,16,18,21,22,24,25,28,30,33,37,40,42,45,48,
57,58,60,70,72,78,85,88,93,102,105,112,120,130,133,165,168,177,190,210,232,
240,253,273,280,312,330,345,357,385,408,462,520,760,840,1320,1365,1848.
*References:*
- [Wikipedia: Idoneal number](https://en.wikipedia.org/wiki/Idoneal_number)
- [OEIS A000926](https://oeis.org/A000926)
-/

namespace Idoneal

/--
Equivalent definition: A positive integer $n$ is idoneal if and only if it cannot be written as
$ab + bc + ac$ for distinct positive integers $a, b,$ and $c$.
-/
def IsIdoneal (n : ℕ) : Prop :=
  0 < n ∧
    ¬ ∃ a b c : ℕ,
      0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c

/--
The 65 known idoneal numbers that are conjectured to be the only idoneal numbers.
-/
def knownIdonealNumbers : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28,
   30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102, 105,
   112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240, 253, 273, 280, 312,
   330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848}

/-- All 65 known idoneal numbers are indeed idoneal. -/
@[category test, AMS 11]
theorem knownIdonealNumbers_are_idoneal : ∀ n ∈ knownIdonealNumbers, IsIdoneal n := by
  sorry

/--
Idoneal numbers completeness conjecture.
-/
@[category research open, AMS 11]
theorem idoneal_numbers_completeness :
    answer(sorry) ↔
      ∀ n : ℕ, IsIdoneal n → n ∈ knownIdonealNumbers := by
  sorry

end Idoneal
