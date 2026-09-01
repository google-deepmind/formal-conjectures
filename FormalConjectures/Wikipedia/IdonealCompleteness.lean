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

/--
Reduces the unbounded search for a representation `n = a*b + b*c + a*c` (with
`0 < a < b < c`) to a *bounded, decidable* double search over `a, b ∈ range (n+1)`.

The third variable is not searched: for a fixed pair `a, b` the equation
`n = a*b + c*(a+b)` pins down `c = (n - a*b) / (a+b)`, so the witness `c` is
recovered by exact division. The forward direction uses `a, b ≤ n` (each pairwise
product is at most `n`) to land the pair in `range (n+1)`.
-/
@[category API, AMS 11]
private theorem exists_triple_iff_bounded (n : ℕ) :
    (∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c) ↔
      (∃ a ∈ Finset.range (n + 1), ∃ b ∈ Finset.range (n + 1),
        0 < a ∧ a < b ∧ b < (n - a * b) / (a + b) ∧
          n = a * b + b * ((n - a * b) / (a + b)) + a * ((n - a * b) / (a + b))) := by
  constructor
  · rintro ⟨a, b, c, ha, hab, hbc, heq⟩
    have hbn : b ≤ n := by nlinarith
    have han : a ≤ n := by nlinarith
    have hsum : n - a * b = c * (a + b) := by
      have : n = a * b + c * (a + b) := by ring_nf; ring_nf at heq; linarith
      omega
    have hpos : 0 < a + b := by omega
    have hc : (n - a * b) / (a + b) = c := by rw [hsum]; exact Nat.mul_div_cancel _ hpos
    exact ⟨a, Finset.mem_range.mpr (by omega), b, Finset.mem_range.mpr (by omega),
      ha, hab, hc ▸ hbc, hc ▸ heq⟩
  · rintro ⟨a, _, b, _, ha, hab, hbc, heq⟩
    exact ⟨a, b, (n - a * b) / (a + b), ha, hab, hbc, heq⟩

set_option maxRecDepth 4096 in
/-- All 65 known idoneal numbers are indeed idoneal. -/
@[category test, AMS 11]
theorem knownIdonealNumbers_are_idoneal : ∀ n ∈ knownIdonealNumbers, IsIdoneal n := by
  intro n hn
  fin_cases hn <;>
    refine ⟨by norm_num, ?_⟩ <;>
    rw [exists_triple_iff_bounded] <;>
    native_decide

/--
Idoneal numbers completeness conjecture.
-/
@[category research open, AMS 11]
theorem idoneal_numbers_completeness :
    answer(sorry) ↔
      ∀ n : ℕ, IsIdoneal n → n ∈ knownIdonealNumbers := by
  sorry

end Idoneal
