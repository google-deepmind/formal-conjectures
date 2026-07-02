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
# Conjectures associated with A211417

Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$

The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.

*References:*
- [A211417](https://oeis.org/A211417)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA211417


/--
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Nat Int Finset

def coprime_indices (r : ℕ) : Finset ℕ :=
  (Finset.range (r + 1)).filter (fun i => 1 ≤ i ∧ Nat.gcd i 30 = 1)

/--
The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.
-/
def divisor_product (n r : ℕ) : ℤ :=
  (coprime_indices r).prod (fun i : ℕ => 30 * (n : ℤ) - (i : ℤ))


@[category test, AMS 11]
lemma a_zero : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 77636318760 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 53837289804317953893960 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 43880754270176401422739454033276880 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 38113558705192522309151157825210540422513019720 := by rfl


/--
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$

The product term in the denominator of the general conjecture:
$$\prod_{i = 1..r, i \text{ coprime to } 30} (30n - i)$$
We define this in ℤ to handle the $n=0$ case where $30n-i$ in the product might be negative.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/211417.wip.lean#L243"]
theorem target_theorem_0
  (n : ℕ) : (30 * (n : ℤ) - 1) ∣ (a n : ℤ) := by
    sorry

end OeisA211417
