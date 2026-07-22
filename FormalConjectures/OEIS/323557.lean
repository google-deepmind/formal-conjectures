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
# Conjectures associated with A323557

A323557: G.f.: $\sum_{n\ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 + x^{n+1})^{n+1}}$.
The $m$-th term $a(m)$ is the coefficient of $x^m$, which is explicitly given by the sum:
$$ a(m) = \sum_{n=0}^m \sum_{k=0}^n \binom{n}{k} (-1)^j \binom{n+j}{j},$$
where $j = \frac{m - n(k+1)}{n+1}$, and the term is zero unless $j$ is a natural number.

*References:*
- [A323557](https://oeis.org/A323557)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA323557


open scoped Classical

open Nat

/--
A323557: G.f.: $\sum_{n\ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 + x^{n+1})^{n+1}}$.
The $m$-th term $a(m)$ is the coefficient of $x^m$, which is explicitly given by the sum:
$$ a(m) = \sum_{n=0}^m \sum_{k=0}^n \binom{n}{k} (-1)^j \binom{n+j}{j},$$
where $j = \frac{m - n(k+1)}{n+1}$, and the term is zero unless $j$ is a natural number.
-/
def a (m : ℕ) : ℤ :=
  Finset.sum (Finset.range (m + 1)) fun n =>
    Finset.sum (Finset.range (n + 1)) fun k =>
      let exp_x_num := n * (k + 1)
      if exp_x_num ≤ m then
        let remainder := m - exp_x_num
        if (n + 1) ∣ remainder then
          let j : ℕ := remainder / (n + 1)
          let c₁ : ℤ := (n.choose k)
          let c₂ : ℤ := (choose (n + j) j)
          let sign : ℤ := if Even j then 1 else -1
          sign * c₁ * c₂
        else
          0
      else
        0


@[category test, AMS 11]
lemma a_zero : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 0 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 3 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = -2 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 2 := by rfl


/--
A323557: G.f.: $\sum_{n\ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 + x^{n+1})^{n+1}}$.
The $m$-th term $a(m)$ is the coefficient of $x^m$, which is explicitly given by the sum:
$$ a(m) = \sum_{n=0}^m \sum_{k=0}^n \binom{n}{k} (-1)^j \binom{n+j}{j},$$
where $j = \frac{m - n(k+1)}{n+1}$, and the term is zero unless $j$ is a natural number.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/323557.wip.lean#L193"]
theorem odd_a_implies_pronic (m : ℕ) : Odd (a m) → ∃ n : ℕ, m = n * (n + 1) := by
    sorry

end OeisA323557
