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

open Nat List Set Function

/--
A helper function to compute the "baseless" value of a sequence of digits $D$ (most significant first).
If $D = [d_k, d_{k-1}, \ldots, d_0]$, the value is computed by
$V_{k} = d_k$. The final result is $V_0 \cdot d_0$, where $V_0$ is accumulated by $V_{i} = V_{i+1} \cdot d_{i+1} + d_i$.
-/
def baseless_value_list (D : List ℕ) : ℕ :=
  match D with
  | [] => 0
  | [_] => 0 -- Single digit numbers A > 1 must have at least 2 digits to be baseless.
  | d_k :: ds_rest =>
    -- The initial state carries (current_value, multiplier_for_next_step).
    let initial_state : ℕ × ℕ := (d_k, d_k)

    -- ds_rest = [d_{k-1}, \ldots, d_0] are the digits for the fold.
    let V_0_and_d_0 : ℕ × ℕ := ds_rest.foldl
      (fun state d_curr =>
        let (V_prev, d_prev_mult) := state
        -- The multiplier for the next step is the digit just added, following the OEIS pattern.
        (V_prev * d_prev_mult + d_curr, d_curr)
      ) initial_state

    let (V₀, d₀) := V_0_and_d_0
    -- Final multiplication by the last digit, d₀.
    V₀ * d₀

/--
$A$ is a "baseless number" in base $b$ if adding and multiplying its base $b$ digits left to right yields $A$.
-/
def is_baseless (b A : ℕ) : Prop :=
  -- We use Nat.digits which is safe for base b >= 2.
  baseless_value_list ((digits b A).reverse) = A

/--
The set of numbers greater than 1 that are baseless in base $n$.
-/
def BaselessSet (n : ℕ) : Set ℕ :=
  { A : ℕ | A > 1 ∧ is_baseless n A }

open scoped Classical in
/--
A334916: $a(n)$ is the smallest number $> 1$ whose base $n$ digits yield the original number
when added and multiplied left to right; or $0$ if no such number exists.
-/
noncomputable def A334916 (n : ℕ) : ℕ :=
  if n < 4 then
    0 -- Bases 1, 2, 3 lead to a(n)=0. Base 1 is ill-defined for digits extraction.
  else
    sInf (BaselessSet n)


theorem a_one : A334916 1 = 0 := by
  simp_all![ A334916]

theorem a_two : A334916 2 = 0 := by
  rfl

theorem a_three : A334916 3 = 0 := by
  rfl

theorem a_four : A334916 4 = 6 := by
  sorry

/--
The number 8385 = ((((8)8+3)3+8)8+5)5 is known to be the unique baseless number in base 10.
The conjecture is that the baseless numbers in base 6 and 10 are unique, and questions
whether another base $n$, other than 6 and 10, has a unique tasteless number.
We formalize the uniqueness claim for $n=6$ and $n=10$ using the unique existence quantifier.
-/
theorem oeis_334916_conjecture_0 :
    (∃! A, A > 1 ∧ is_baseless 6 A) ∧ (∃! A, A > 1 ∧ is_baseless 10 A) ∧
    -- Formalizing the open question part: "Are there number bases n, other than 6 and 10, that have a unique example?"
    (∃ n > 1, n ≠ 6 ∧ n ≠ 10 ∧ (∃! A, A > 1 ∧ is_baseless n A)) := by sorry
