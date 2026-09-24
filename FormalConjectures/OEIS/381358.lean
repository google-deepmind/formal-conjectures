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
# Row sums of irregular triangle A381587

Row sums of the irregular triangle A381587, defined via run lengths of digital sequences.

*References:*
- [A381358](https://oeis.org/A381358)
-/
open List Nat

namespace OeisA381358

/-- Computes the run lengths of a list of natural numbers. -/
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

/--
A381587 $T_n$: The $n$-th row of the irregular triangle, following the recurrence:
$T_1=[1], T_2=[1], T_3=[2]$. For $n \ge 4$, $T_n = \text{Runs}(\text{Reverse}(T_{n-1})) \frown
T_{n-1}$.
$n$ is 1-indexed here.
-/
private def t : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 => -- Covers indices >= 4. Recurses on k+3, which is n-1.
    let prev_T := t (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

/--
Row sums of irregular triangle A381587.
-/
def a (n : ℕ) : ℕ :=
  (t n).sum

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  symm
  norm_num [a]
  norm_num [t]
  simp_all [run_lengths_nat]

/--
If it exists, the limit of $\mathrm{a}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/
@[category research open, AMS 11]
theorem limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
by sorry

end OeisA381358
