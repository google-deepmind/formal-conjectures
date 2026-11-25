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
module

public import FormalConjecturesUtil

/-!
# Green's Open Problem 36

*References:*
* [Gr24] [Green's Open Problems #36](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.36)
* [CKSU05] H. Cohn, R. Kleinberg, B. Szegedy, and C. Umans,
  [*Group-theoretic Algorithms for Matrix Multiplication*](https://arxiv.org/abs/math/0511460),
  Theorem 4.4 and Conjecture 4.7.
* [OAI26] OpenAI, [*The matrix multiplication exponent is nine fourths*](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf),
  Theorem 1.1.
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Green36

/-- The simultaneous double product property [CKSU05, Definition 4.1]. -/
def SimultaneousDoubleProduct {ι H : Type*} [AddCommGroup H]
    (A B : ι → Finset H) : Prop :=
  open scoped Classical in
  (∀ i, (A i + B i).card = (A i).card * (B i).card) ∧
  (∀ i j k, i ≠ k → Disjoint (A i + B j) (A j + B k))

/-- A variant of the simultaneous double product property, as stated in [Gr24, Problem 36]. -/
def Green36Property {ι H : Type*} [AddCommGroup H]
    (A B : ι → Finset H) : Prop :=
  open scoped Classical in
  (∀ i, (A i + B i).card = (A i).card * (B i).card) ∧
  (∀ i j k, j ≠ k → Disjoint (A i + B i) (A j + B k))

/--
Do the following exist, for arbitrarily large $n$? An abelian group $H$ with $|H| = n^{2+o(1)}$,
together with subsets $A_1, ..., A_n, B_1, ..., B_n$ satisfying $|A_i||B_i| \ge n^{2-o(1)}$ and
$|A_i + B_i| = |A_i||B_i|$, such that the sets $A_i + B_i$ are disjoint from the sets $A_j + B_k$
($j \neq k$)?

No. Negating the sets $B_i$ converts this to the simultaneous double product property in
[CKSU05, Definition 4.1]. Such families would force the matrix multiplication exponent to be $2$
by [CKSU05, Theorem 4.4], whereas [OAI26, Theorem 1.1] gives $9/4$.
-/
@[category research solved, question, AMS 5 20]
theorem green_36 :
    ¬ ∀ ε > (0 : ℝ), ∃ᶠ n in atTop,
      ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H) (A B : Fin n → Finset H),
        (n : ℝ) ^ (2 - ε) ≤ Nat.card H ∧ Nat.card H ≤ (n : ℝ) ^ (2 + ε) ∧
        (∀ i, (n : ℝ) ^ (2 - ε) ≤ (A i).card * (B i).card) ∧
        Green36Property A B := by
  sorry

/-- The answer is also no for the simultaneous double product property as stated in
[CKSU05, Definition 4.1]. -/
@[category research solved, question, AMS 5 20]
theorem green_36.variants.cks05 :
    ¬ ∀ ε > (0 : ℝ), ∃ᶠ n in atTop,
      ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H) (A B : Fin n → Finset H),
        (n : ℝ) ^ (2 - ε) ≤ Nat.card H ∧ Nat.card H ≤ (n : ℝ) ^ (2 + ε) ∧
        (∀ i, (n : ℝ) ^ (2 - ε) ≤ (A i).card * (B i).card) ∧
        SimultaneousDoubleProduct A B := by
  sorry

-- TODO(jeangud) Add variants mentioned in [Gr24, Problem 36] comments.

end Green36
