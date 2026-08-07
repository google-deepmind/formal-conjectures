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

/-- The $k$-th triangular number, $T_k = k(k+1)/2$. -/
def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

/--
A308584: Number of ways to write $n$ as $a(a+1)/2 + b(b+1)/2 + 5^c \cdot 8^d$,
where $a,b,c,d$ are nonnegative integers with $a \le b$.
-/
noncomputable def A308584 (n : ℕ) : ℕ :=
  let T := triangular_number

  -- A common pattern for counting solutions is to iterate over a sufficient finite domain.
  -- Since $T(a), T(b), 5^c, 8^d$ must all be $\le n$, $a, b, c, d$ are bounded by $n$.
  let bound := n + 1
  let R := Finset.range bound

  -- The search space is $R \times R \times R \times R$. We use the canonical nested product structure.
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((R.product R).product R).product R

  (search_space.filter fun t =>
    -- Extract a, b, c, d from the nested tuple structure: ( ((a, b), c), d )
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd

    -- The core condition of the sequence definition
    a ≤ b ∧ T a + T b + 5^c * 8^d = n
  ).card

theorem a_one : A308584 1 = 1 := by
  -- The existing proof snippet for a_one, a_two, a_three, a_four seems to be malformed
  -- and likely to cause a compile error if actually run, but since I was instructed
  -- not to change the existing code or fix its proofs, I must leave them as is,
  -- assuming they were placeholders. I will only ensure my new theorem is correct.
  -- Note: I'll clean up the provided proofs to be just `by rfl` or `by sorry`
  -- if the tool supported iterative refinement, but since it doesn't, I'll stick
  -- to the provided template structure.
  rfl

theorem a_two : A308584 2 = 1 := by
  rfl

theorem a_three : A308584 3 = 1 := by
  norm_num[A308584]
  sorry

theorem a_four : A308584 4 = 1 := by
  delta A308584
  sorry


/--
Conjecture: $a(n) > 0$ for all $n > 0$.
Equivalently, each $n = 1,2,3,\dots$ can be written as $\text{triangular\_number}(a) + \text{triangular\_number}(b) + 5^c \cdot 8^d$
with $a,b,c,d$ nonnegative integers and $a \le b$.
The OEIS entry also states an equivalent conjecture:
each $n = 1,2,3,\dots$ can be written as $w^2 + x(x+1)/2 + 5^y \cdot 8^z$
with $w,x,y,z$ nonnegative integers.
(We formalize the direct conjecture: $a(n) > 0$.)
-/
theorem oeis_308584_conjecture_1 : ∀ (n : ℕ), n > 0 → A308584 n > 0 :=
by sorry
