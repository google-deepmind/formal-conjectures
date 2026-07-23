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

open Nat Finset

/--
A352628: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 2d^4 + 3c^2d^2$,
where $a,b,c,d$ are nonnegative integers.
-/
def A352628 (n : ℕ) : ℕ :=
  -- A sufficient bound for all variables.
  -- Note: c^4 and 2*d^4 are the largest terms, so c, d are roughly bounded by n^(1/4).
  -- range (n+1) is a very loose but safe upper bound.
  let S : Finset ℕ := range (n + 1)

  -- The search space is $S \times S \times S \times S$
  let Q := S.product (S.product (S.product S))

  -- The number of ways is the sum of 1 for each tuple that satisfies the equation.
  Q.sum fun p =>
    let a := p.fst
    let p_bcd := p.snd
    let b := p_bcd.fst
    let p_cd := p_bcd.snd
    let c := p_cd.fst
    let d := p_cd.snd

    -- Match the target equation exactly. The expression is equivalent to
    -- a^2 + 2*b^2 + (c^2 + d^2) * (c^2 + 2*d^2)
    let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
    if E = n then 1 else 0

/--
Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each nonnegative integer can be written as a^2 + 2b^2 + (c^2+d^2)*(c^2+2d^2) with a,b,c,d integers.
-/
theorem oeis_352628_conjecture_1 (n : ℕ) : A352628 n > 0 :=
  by sorry
