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
# Sums of four binary palindromes

Number of ordered quadruples $(u, v, w, x)$ of binary palindromes (see A006995) with
$u + v + w + x = n$.

*References:*
- [A261680](https://oeis.org/A261680)
- [Sums of Palindromes: an Approach via Nested-Word Automata](https://arxiv.org/abs/1706.10206)
  by *Aayush Rajasekaran*, *Jeffrey Shallit*, and *Tim Smith*, arXiv:1706.10206 (2017)
-/

namespace OeisA261680

/-- Whether $k$ is a binary palindrome (A006995). -/
def isBinaryPalindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

/--
The number of ordered quadruples $(u, v, w, x)$ of binary palindromes with $u + v + w + x = n$.
-/
def a (n : ℕ) : ℕ :=
  ∑ u ∈ Finset.range (n + 1),
    ∑ v ∈ Finset.range (n - u + 1),
      ∑ w ∈ Finset.range (n - (u + v) + 1),
        let x := n - (u + v + w)
        if isBinaryPalindrome u &&
           isBinaryPalindrome v &&
           isBinaryPalindrome w &&
           isBinaryPalindrome x
        then 1 else 0

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 6 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 8 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 13 := by rfl

/--
Every number is the sum of four binary palindromes, i.e., $a(n) > 0$ for all $n$.
Originally stated as a conjecture on OEIS; proved by Rajasekaran, Shallit, and Smith (2017).
-/
@[category research solved, AMS 11]
theorem conjecture (n : ℕ) : 0 < a n := by
  sorry

end OeisA261680
