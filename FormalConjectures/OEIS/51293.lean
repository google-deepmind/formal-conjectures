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
# Asymptotics of subsets of $\{1, 2, \dots, n\}$ with integer average

Number of nonempty subsets of $\{1, 2, 3, \dots, n\}$ whose elements have an integer average.

Benoit Cloitre conjectured the asymptotic expansion:
$$a(n) = \frac{2^{n+1}}{n} \left(1 + \frac{1}{n} + \frac{3}{n^2} + \frac{13}{n^3} + \frac{75}{n^4} + \frac{541}{n^5} + o\left(\frac{1}{n^5}\right)\right)$$
where the coefficients $1, 1, 3, 13, 75, 541, \dots$ are the Fubini numbers (preferential arrangements, A000670).

*References:*
- [A051293](https://oeis.org/A051293)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
- [A000670](https://oeis.org/A000670)
-/

namespace OeisA51293


open Polynomial

open scoped Topology

open Finset Nat Real Filter Asymptotics

/--
Number of nonempty subsets of $\{1, 2, 3, \dots, n\}$ whose elements have an integer average.
-/
def a (n : ℕ) : ℕ :=
  Finset.card (
    (Finset.Icc 1 n).powerset.filter fun S : Finset ℕ =>
      S.Nonempty ∧ S.card ∣ S.sum id
  )

def aReal (n : ℕ) : ℝ := a n


@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma a_2 : a 2 = 2 := by rfl

@[category test, AMS 11]
lemma a_3 : a 3 = 5 := by rfl

@[category test, AMS 11]
lemma a_4 : a 4 = 8 := by rfl

@[category test, AMS 11]
lemma a_5 : a 5 = 15 := by rfl


/--
Conjecture: $a(n) = 2^{n+1}/n \cdot (1 + 1/n + 3/n^2 + 13/n^3 + 75/n^4 + 541/n^5 + o(1/n^5))$. - _Benoit Cloitre_, Oct 20 2002

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/51293.wip.lean#L503"]
theorem tendsto_aReal_asymptotic :
    Tendsto (fun n : ℕ =>
      (aReal n - (2 ^ (n + 1) / (n : ℝ)) *
        (1 + 1 / (n : ℝ) + 3 / (n : ℝ) ^ 2 + 13 / (n : ℝ) ^ 3 + 75 / (n : ℝ) ^ 4 + 541 / (n : ℝ) ^ 5)) /
      (2 ^ (n + 1) / (n : ℝ) ^ 6)) atTop (nhds 0) := by
    sorry

end OeisA51293
