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
open List Nat Filter Real

/--
A330731: Binary sequence created by greedily remaining as normal as possible:
starting with the empty sequence, repeatedly find the longest tail (or suffix) which is followed
by one digit more frequently than the other, and append the digit which follows said tail less often.
0 is appended if no such inequality is found.
-/
noncomputable def A330731 : ℕ → ℕ
| n =>
  -- S is the sequence generated so far: (A(0), ..., A(n-1))
  let S : List ℕ := List.ofFn (fun i : Fin n => A330731 i.val)

  -- Function to count occurrences of P as a sublist (contiguous block) in S.
  -- This is equivalent to counting how many "tail-extensions" of S start with P.
  let count_sublist (P S : List ℕ) : ℕ :=
    (List.tails S).countP (fun l => P.isPrefixOf l)

  -- Recursive search for the longest tail T (length L >= 1) that biases the next digit.
  -- L_len is the remaining length to check.
  let rec check_tail (L_len : ℕ) : Option ℕ :=
    match L_len with
    | 0 => none -- Done with non-empty tails.
    | L' + 1 =>
      let L := L' + 1 -- L is the current length of T

      -- T is the suffix of S of length L.
      let T := S.drop (n - L)

      let P0 := T ++ [0]
      let P1 := T ++ [1]

      -- N_T(b) is the number of times T followed by b appears in S.
      let N0 := count_sublist P0 S
      let N1 := count_sublist P1 S

      if N0 ≠ N1 then
        -- Found the longest tail. Append the less frequent digit.
        if N0 < N1 then some 0 else some 1
      else
        -- Continue the search with a shorter tail L' < L.
        check_tail L'

  -- Start search from the maximum non-empty tail length, which is n.pred (n-1).
  let max_L := n.pred

  match check_tail max_L with
  | some d => d
  | none =>
    -- Fallback to empty tail case (L = 0). T = [].
    let N0_empty := count_sublist [0] S;
    let N1_empty := count_sublist [1] S;

    if N0_empty ≠ N1_empty then
      -- Append less frequent digit in S.
      if N0_empty < N1_empty then 0 else 1
    else
      -- Final default case: 0 is appended if no such inequality is found at any level.
      0
/-! The original placeholder theorems are removed to focus on the core task and avoid complex error diagnostics -/

/--
The count of occurrences of the word `w` in the prefix of `A330731` of length `N`.
Specifically, the number of times `w` appears as a contiguous sublist starting at index `i < N - w.length + 1`.
-/
noncomputable def OEIS_count_word (w : List ℕ) (N : ℕ) : ℕ :=
  if N ≥ w.length then
    let S := List.ofFn (fun i : Fin N => A330731 i.val);
    (List.tails S).countP (fun l => w.isPrefixOf l)
  else 0

/--
A predicate stating that the word `w` appears in A330731 with the correct asymptotic frequency.
-/
noncomputable def A330731_asymptotic_freq (w : List ℕ) : Prop :=
  let k := w.length;
  let expected_freq : Real := 1 / (2^k : ℝ);
  Tendsto
    (fun (N : ℕ) =>
      (OEIS_count_word w N : ℝ) / ((max 1 (N - k + 1)) : ℝ))
    atTop
    (nhds expected_freq)

/--
A sequence $a: \mathbb{N} \to \{0, 1\}$ is normal if every non-empty finite binary word $w$
appears in $a$ with asymptotic frequency $1/2^{\text{length}(w)}$.
We ensure $w$ is composed only of 0s and 1s.
-/
def is_normal_A330731 : Prop :=
  ∀ (w : List ℕ), w.length > 0 ∧ (∀ x ∈ w, x = 0 ∨ x = 1) →
  A330731_asymptotic_freq w

/--
A330731 a(n) is conjectured to be normal by virtue of its construction.
-/
theorem oeis_330731_conjecture_0 : is_normal_A330731 := by
  sorry
