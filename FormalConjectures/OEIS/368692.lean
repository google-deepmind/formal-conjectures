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
# Conjectures associated with A368692

A368692:
$$a(n) = \frac{(12n + 6)! \cdot (6n + 9)!}{108 \cdot (4n + 2)! \cdot
(2n + 3)! \cdot ((6n + 5)!)^2}$$
It is conjectured that $a(n)$ are integers.

*References:*
- [A368692](https://oeis.org/A368692)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA368692


open Nat

/--
A368692:
$$a(n) = \frac{(12n + 6)! \cdot (6n + 9)!}{108 \cdot (4n + 2)! \cdot
(2n + 3)! \cdot ((6n + 5)!)^2}$$
It is conjectured that $a(n)$ are integers.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := (12 * n + 6)! * (6 * n + 9)!
  let den_base : ℕ := (4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2
  num / (108 * den_base)


@[category test, AMS 11]
lemma a_zero : a 0 = 14 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 563108 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 54231252075 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 6700034035890000 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 928978310614152999200 := by rfl


/--
A368692:
$$a(n) = \frac{(12n + 6)! \cdot (6n + 9)!}{108 \cdot (4n + 2)! \cdot
(2n + 3)! \cdot ((6n + 5)!)^2}$$
It is conjectured that $a(n)$ are integers.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/368692.wip.lean#L158"]
theorem a_is_int (n : ℕ) : 108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!) ^ 2) ∣
    (12 * n + 6)! * (6 * n + 9)! := by
    sorry

end OeisA368692
