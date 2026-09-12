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
# Maximal run lengths in the second MSB of Tribonacci numbers $T(n)$

The Tribonacci numbers $T_n$ (A000073).
$T_0=0, T_1=0, T_2=1$, and $T_n = T_{n-1} + T_{n-2} + T_{n-3}$ for $n \ge 3$.

Second most significant bit of the tribonacci number A000073(n).
This is formalized by extracting the bit at position $\lfloor \log_2 T_n \rfloor - 1$.

*References:*
- [A271591](https://oeis.org/A271591)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
- [A000073](https://oeis.org/A000073)
-/

namespace OeisA271591


open Nat

/--
The Tribonacci numbers $T_n$ (A000073).
$T_0=0, T_1=0, T_2=1$, and $T_n = T_{n-1} + T_{n-2} + T_{n-3}$ for $n \ge 3$.
-/
def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

/--
Second most significant bit of the tribonacci number A000073(n).
This is formalized by extracting the bit at position $\lfloor \log_2 T_n \rfloor - 1$.
-/
def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  -- The index of the MSB is T.log2. The index of the second MSB is T.log2 - 1.
  if T ≤ 1 then
    0
  else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

def IsMaximalRun (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧
  -- The run consists of L consecutive $v$'s starting at n
  (∀ i : ℕ, i < L → a (n + i) = v) ∧
  -- The run is not followed by $v$
  (a (n + L) ≠ v) ∧
  -- The run is not preceded by $v$
  (a (n - 1) ≠ v)


@[category test, AMS 11]
lemma a_4 : a 4 = 0 := by rfl

@[category test, AMS 11]
lemma a_5 : a 5 = 0 := by rfl

@[category test, AMS 11]
lemma a_6 : a 6 = 1 := by rfl

@[category test, AMS 11]
lemma a_7 : a 7 = 1 := by rfl

@[category test, AMS 11]
lemma a_8 : a 8 = 1 := by rfl


/--
It is conjectured that after the first two 0's, the number of consecutive 0's is only 4 or 5, and the number of consecutive 1's is only 3 or 4 (tested up to $n = 10^4$).

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/271591.wip.lean#L497"]
theorem maximal_run_lengths : (∀ n L, IsMaximalRun 0 n L → (L = 4 ∨ L = 5)) ∧
    (∀ n L, IsMaximalRun 1 n L → (L = 3 ∨ L = 4)) := by
    sorry

end OeisA271591
