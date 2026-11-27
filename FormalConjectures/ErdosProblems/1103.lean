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
# Erdős Problem 1103

*References:*
- [erdosproblems.com/1103](https://www.erdosproblems.com/1103)
- [Er81h] P. Erdős, *Some problems and results on additive and multiplicative number theory*,
  Analytic number theory (Philadelphia, 1980), Lecture Notes in Math. 899 (1981), 171–182.
- [vDTa25] W. van Doorn and T. Tao, *Growth rates of sequences governed by the squarefree
  properties of its translates*, [arXiv:2512.01087](https://arxiv.org/abs/2512.01087) (2025).
-/

@[expose] public section

open Filter
open scoped Pointwise

namespace Erdos1103

/-- Every element of `A + A` is squarefree. This includes the sums $a + a$. -/
def HasSquarefreeSums (A : Set ℕ) : Prop :=
  ∀ n ∈ A + A, Squarefree n

/-- A set with squarefree sums does not contain $0$, since $0 + 0 = 0$ is not squarefree. -/
@[category test, AMS 11]
theorem zero_notMem_of_hasSquarefreeSums {A : Set ℕ} (h : HasSquarefreeSums A) : 0 ∉ A :=
  fun h0 => not_squarefree_zero (h 0 (Set.add_mem_add h0 h0))

/--
Let $A$ be an infinite sequence of integers such that every $n \in A + A$ is squarefree. How fast
must $A$ grow?

Erdős notes that such a sequence can grow exponentially, and does not expect one of polynomial
growth. This theorem formalizes the question whether no such $A = \{a_1 < a_2 < \cdots\}$ has
$a_j \ll j^C$ for any $C > 0$.
-/
@[category research open, question, AMS 11]
theorem erdos_1103 :
    ∀ A : Set ℕ, A.Infinite → HasSquarefreeSums A → ∀ C > (0 : ℝ),
      ¬ ((fun j : ℕ => (Nat.nth (· ∈ A) j : ℝ)) ≪ fun j : ℕ => (j : ℝ) ^ C) := by
  sorry

/--
van Doorn and Tao [vDTa25, Theorem 8 of v1]: every infinite $A = \{a_1 < a_2 < \cdots\}$ with
squarefree sums has $a_j \gg j^{4/3}$.
-/
@[category research solved, AMS 11]
theorem erdos_1103.variants.lower (A : Set ℕ) (hA : A.Infinite) (h : HasSquarefreeSums A) :
    (fun j : ℕ => (j : ℝ) ^ ((4 : ℝ) / 3)) ≪ fun j : ℕ => (Nat.nth (· ∈ A) j : ℝ) := by
  sorry

/--
van Doorn and Tao [vDTa25, Theorem 7 of v1]: there are an absolute constant $C$ and an infinite
$A = \{a_1 < a_2 < \cdots\}$ with squarefree sums such that $a_j \le \exp(Cj / \log j)$ for all
$j \ge 2$. Here $a_j$ is `Nat.nth (· ∈ A) (j - 1)`.
-/
@[category research solved, AMS 11]
theorem erdos_1103.variants.upper :
    ∃ C : ℝ, ∃ A : Set ℕ, A.Infinite ∧ HasSquarefreeSums A ∧
      ∀ j ≥ 2, (Nat.nth (· ∈ A) (j - 1) : ℝ) ≤ Real.exp (C * j / Real.log j) := by
  sorry

/--
Erdős [Er81h] asked whether there is an infinite $A$ such that, for every $a \in A$ and prime $p$,
if $a \equiv t \pmod{p^2}$ with $0 \le t < p^2$ then $1 \le t < p^2 / 2$. Such an $A$ has squarefree
sums. The answer is no: if $p$ is a prime with $a < p^2 \le 2a$, then $t = a \ge p^2 / 2$, and such
a prime exists for all large $a$.
-/
@[category research solved, AMS 11]
theorem erdos_1103.variants.mod_sq :
    ¬ ∃ A : Set ℕ, A.Infinite ∧
      ∀ a ∈ A, ∀ p : ℕ, p.Prime → 1 ≤ a % p ^ 2 ∧ 2 * (a % p ^ 2) < p ^ 2 := by
  sorry

end Erdos1103
