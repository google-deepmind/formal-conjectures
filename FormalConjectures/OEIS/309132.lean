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
# Conjectures associated with A309132

A309132: a(n) is the denominator of F(n) = A027641(n-1)/n + A027642(n-1)/n^2.

Definition of a Carmichael number $n$: a composite number s.t.
$b^{n-1} \equiv 1 \pmod n$ for all $b$ coprime to $n$.

*References:*
- [A309132](https://oeis.org/A309132)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
- [A027641](https://oeis.org/A027641)
- [A027642](https://oeis.org/A027642)
-/

namespace OeisA309132


open Rat Nat

/--
A309132: a(n) is the denominator of F(n) = A027641(n-1)/n + A027642(n-1)/n^2.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let n_q : ℚ := n
    let B_nm1 : ℚ := bernoulli (n - 1)
    let F_n : ℚ := (B_nm1.num : ℚ) / n_q + (B_nm1.den : ℚ) / (n_q * n_q)
    F_n.den

/-- Definition of a Carmichael number $n$: a composite number s.t.
$b^{n-1} \equiv 1 \pmod n$ for all $b$ coprime to $n$. -/
def is_carmichael_number (n : ℕ) : Prop :=
  (¬ Nat.Prime n ∧ n > 1) ∧ (∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n])

/-- Helper definition for "composite number" -/
def is_composite (n : ℕ) : Prop := ¬ Nat.Prime n ∧ n > 1


@[category test, AMS 11]
lemma a_one : a 1 = 1 := by delta a; norm_num [bernoulli]

@[category test, AMS 11]
lemma a_two : a 2 = 1 := by delta a; norm_num [bernoulli]

@[category test, AMS 11]
lemma a_three : a 3 = 1 := by delta a; norm_num [bernoulli]

@[category test, AMS 11]
lemma a_four : a 4 = 16 := by delta a; norm_num [bernoulli]

@[category test, AMS 11]
lemma a_five : a 5 = 1 := by delta a; norm_num [bernoulli]


/--
A309132: a(n) is the denominator of F(n) = A027641(n-1)/n + A027642(n-1)/n^2.

Definition of a Carmichael number $n$: a composite number s.t.
$b^{n-1} \equiv 1 \pmod n$ for all $b$ coprime to $n$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/309132.wip.lean#L353"]
theorem carmichael_iff_squarefree_a :
    ∀ (n : ℕ), (is_composite n ∧ Squarefree (a n)) ↔ is_carmichael_number n := by
    sorry

end OeisA309132
