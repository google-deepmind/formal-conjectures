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
# a(n) = the number of values of k <= 10^n such that sqrt(k*(k+1)*(k+2)*(k+3)+1) is prime.

a(n) = the number of values of k <= 10^n such that sqrt(k*(k+1)*(k+2)*(k+3)+1) is prime.
Since $\sqrt{k(k+1)(k+2)(k+3)+1} = k^2 + 3k + 1$,
$a(n) = \#\{k \in \mathbb{N} \mid 1 \le k \le 10^n \land (k^2 + 3k + 1) \text{ is prime} \}.$

*References:*
- [A115366](https://oeis.org/A115366)
-/

namespace OeisA115366

open Filter Real Topology

/--
The primary defining sequence `a`.
$a(n) = \#\{k \in \mathbb{N} \mid 1 \le k \le 10^n \land (k^2 + 3k + 1) \text{ is prime} \}.$
-/
def a (n : ℕ) : ℕ :=
  Finset.card <|
    Finset.filter
      (fun k : ℕ => Nat.Prime (k ^ 2 + 3 * k + 1))
      (Finset.Icc 1 (10 ^ n))

@[category test, AMS 11]
lemma test_a_0 : a 0 = 1 := by native_decide

@[category test, AMS 11]
lemma test_a_1 : a 1 = 9 := by native_decide

/--
Conjecture: a(n)/A006880(n) -> 1.77...
where A006880(n) is the number of primes <= 10^n.
-/
@[category research open, AMS 11]
theorem main_conjecture :
    ∃ L : ℝ,
      Tendsto (fun n : ℕ => (a n : ℝ) / (Nat.primeCounting' (10 ^ n) : ℝ)) atTop (nhds L) ∧
      1.77 ≤ L ∧ L ≤ 1.78 := by
  sorry

end OeisA115366
