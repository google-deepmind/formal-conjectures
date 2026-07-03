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
# Conjectures associated with A325046

A325046: G.f.: $\sum_{n \ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 - x^{n+1})^{n+1}}$.

The term $a(N)$ is the coefficient of $x^N$ in the generating function.
Expanding the terms, we get a formula for $a(N)$:
$$a(N) = \sum_{n=0}^N \sum_{k=0}^n \mathbf{1}_{n + nk + (n+1)j = N} \binom{n}{k} \binom{n+j}{j}$$
where $j = \frac{N - n(k+1)}{n+1}$.

*References:*
- [A325046](https://oeis.org/A325046)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA325046


open Nat

open Finset

/--
A325046: G.f.: $\sum_{n \ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 - x^{n+1})^{n+1}}$.

The term $a(N)$ is the coefficient of $x^N$ in the generating function.
Expanding the terms, we get a formula for $a(N)$:
$$a(N) = \sum_{n=0}^N \sum_{k=0}^n \mathbf{1}_{n + nk + (n+1)j = N} \binom{n}{k} \binom{n+j}{j}$$
where $j = \frac{N - n(k+1)}{n+1}$.
-/
def a (N : ℕ) : ℕ :=
  -- The outer sum runs over $n$ from $0$ to $N$.
  (range (N + 1)).sum (fun n =>
    -- The inner sum runs over $k$ from $0$ to $n$.
    (range (n + 1)).sum (fun k =>
      let R : ℕ := N - n * (k + 1)
      let m : ℕ := n + 1
      -- We require $R = N - n(k+1) \ge 0$ and $m = n+1$ must divide $R$.
      if n * (k + 1) ≤ N ∧ R % m = 0 then
        -- $j = R / m$.
        let j : ℕ := R / m
        -- The summand is $\binom{n}{k} \binom{n+j}{j}$.
        n.choose k * (n + j).choose j
      else
        0
    )
  )


@[category test, AMS 11]
lemma a_zero : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 2 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 3 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 4 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 6 := by rfl


/--
A325046: G.f.: $\sum_{n \ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 - x^{n+1})^{n+1}}$.

The term $a(N)$ is the coefficient of $x^N$ in the generating function.
Expanding the terms, we get a formula for $a(N)$:
$$a(N) = \sum_{n=0}^N \sum_{k=0}^n \mathbf{1}_{n + nk + (n+1)j = N} \binom{n}{k} \binom{n+j}{j}$$
where $j = \frac{N - n(k+1)}{n+1}$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/325046.wip.lean#L166"]
theorem odd_a_implies_pronic (N : ℕ) : a N % 2 = 1 → ∃ k : ℕ, N = k * (k + 1) := by
    sorry

end OeisA325046
