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
# Denominators of $\sum_{k=1}^n \frac{1}{k 2^k}$

$a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$

*References:*
- [A175386](https://oeis.org/A175386)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA175386


/--
$a(n)$ is the denominator of the sum
$$\sum_{i=1}^n \frac{1}{i} \binom{2n-i-1}{i-1}$$
-/
def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.Icc 1 n) fun i : ℕ =>
    -- The upper index is $2n - i - 1$, which is equivalent to
    -- $2n - (i+1)$ in $\mathbb{N}$ for $i \le n$.
    -- The lower index $i-1$ is standard subtraction in $\mathbb{N}$.
    let num : ℕ := Nat.choose (2 * n - (i + 1)) (i - 1)
    (num : ℚ) / (i : ℚ)
  ).den

@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
lemma a_2 : a 2 = 2 := by native_decide

@[category test, AMS 11]
lemma a_3 : a 3 = 6 := by native_decide

@[category test, AMS 11]
lemma a_4 : a 4 = 4 := by native_decide

@[category test, AMS 11]
lemma a_5 : a 5 = 5 := by native_decide


/--
We conjecture that $\sum_{i=1}^{n} \frac{1}{i} \binom{2n-i-1}{i-1}$ is not an integer for $n > 1$.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/175386.wip.lean#L304"]
theorem a_ne_one (n : ℕ) (hn : 1 < n) : a n ≠ 1 := by
    sorry

end OeisA175386
