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
# Conjectures associated with a

a: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.

*References:*
- [A289411](https://oeis.org/A289411)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
- [A007953](https://oeis.org/A007953)
-/

namespace OeisA289411


open Nat

/--
a: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.
-/
def a (n : ℕ) : ℕ :=
  let digital_sum_ten (m : ℕ) : ℕ := (Nat.digits 10 m).sum
  (Finset.range (n + 1)).sum (fun k =>
    Int.sign ((digital_sum_ten (5 * k) : ℤ) - (digital_sum_ten k : ℤ)))
  |>.toNat



@[category test, AMS 11]
lemma a_zero : a 0 = 0 := by native_decide

@[category test, AMS 11]
lemma a_one : a 1 = 1 := by native_decide

@[category test, AMS 11]
lemma a_two : a 2 = 0 := by native_decide

@[category test, AMS 11]
lemma a_three : a 3 = 1 := by native_decide

@[category test, AMS 11]
lemma a_four : a 4 = 0 := by native_decide


/--
a: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/289411.wip.lean#L167"]
theorem a_symm (k : ℕ) (hk : 0 < k) :
    let m_k : ℕ := (10 ^ k) / 2 - 1
    ∀ i : ℕ, i ≤ m_k → a (m_k - i) = a (m_k + i) := by
    sorry

end OeisA289411
