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
# Conjectures associated with A51293

a: Number of nonempty subsets of $\{1, 2, 3, \dots, n\}$ whose elements have an integer average.

`S_real n k` is the number of $k$-element subsets of $\{1, 2, \dots, n\}$
whose sum is divisible by $k$.
By the roots of unity filter, this exact count can be written as:
$S_{n,k} = \frac{1}{k} \sum_{j=0}^{k-1} \sum_{A \in \binom{n}{k}} \omega^{j \sum A}$.
The main term $j=0$ yields exactly $\frac{1}{k} \binom{n}{k}$.
For $j > 0$, the roots of unity evaluated over the subsets yield bounded periodic sums.
The maximal magnitude of these periodic products is achieved when the order of the root is 2,
which bounds the error term magnitude strictly by $2 \cdot 2^{n/2}$.

*References:*
- [A51293](https://oeis.org/A51293)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA51293


open Polynomial

open scoped Topology

/-
Copyright 2025 Google LLC

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

open Finset Nat Real Filter Asymptotics

/--
a: Number of nonempty subsets of $\{1, 2, 3, \dots, n\}$ whose elements have an integer average.
-/
def a (n : ℕ) : ℕ :=
  Finset.card (
    (Finset.Icc 1 n).powerset.filter fun S : Finset ℕ =>
      S.Nonempty ∧ S.card ∣ S.sum id
  )

noncomputable def a_real (n : ℕ) : ℝ := a n


@[category test, AMS 11]
lemma a_one : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 2 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 5 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 8 := by rfl

@[category test, AMS 11]
lemma a_five : a 5 = 15 := by rfl


/--
a: Number of nonempty subsets of $\{1, 2, 3, \dots, n\}$ whose elements have an integer average.

`S_real n k` is the number of $k$-element subsets of $\{1, 2, \dots, n\}$
whose sum is divisible by $k$.
By the roots of unity filter, this exact count can be written as:
$S_{n,k} = \frac{1}{k} \sum_{j=0}^{k-1} \sum_{A \in \binom{n}{k}} \omega^{j \sum A}$.
The main term $j=0$ yields exactly $\frac{1}{k} \binom{n}{k}$.
For $j > 0$, the roots of unity evaluated over the subsets yield bounded periodic sums.
The maximal magnitude of these periodic products is achieved when the order of the root is 2,
which bounds the error term magnitude strictly by $2 \cdot 2^{n/2}$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/51293.wip.lean#L503"]
theorem target_theorem_0
  : Tendsto (fun n : ℕ => (a_real n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) *
      ((1 : ℝ) + 1 / (n : ℝ) + 3 / ((n : ℝ) ^ 2) + 13 / ((n : ℝ) ^ 3) +
        75 / ((n : ℝ) ^ 4) + 541 / ((n : ℝ) ^ 5))) /
      (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))) atTop (nhds 0) := by
    sorry

end OeisA51293
