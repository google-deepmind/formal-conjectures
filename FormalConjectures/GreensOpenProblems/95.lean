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
# Ben Green's Open Problem 95

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.95)
- [CLB18] Cilleruelo, J., Luca, F. and Baxter, L., *Every positive integer is a sum of three
  palindromes*. Math. Comp. 87 (2018), 3023--3055.
  [arXiv:1602.06208](https://arxiv.org/abs/1602.06208)
- [Za24] Zakharov, D., *Most integers are not a sum of two palindromes*. Math. Proc. Cambridge
  Philos. Soc. 177 (2024), 363--366. [arXiv:2402.10808](https://arxiv.org/abs/2402.10808)
-/

@[expose] public section

open Filter

namespace Green95

/--
`IsPalindrome g m` says that the base-`g` digits of `m` read the same in both directions.

Since `Nat.digits g 0 = []`, the number $0$ is a palindrome. This is the convention of
[CLB18, Section 2]. For $g \le 1$ every number is a palindrome, so only bases $g \ge 2$ are of
interest.
-/
def IsPalindrome (g m : ℕ) : Prop :=
  (Nat.digits g m).reverse = Nat.digits g m

/-- `sumsOfTwo g` is the set of numbers $p + q$ with $p, q$ base-`g` palindromes ($0$ allowed). -/
def sumsOfTwo (g : ℕ) : Set ℕ :=
  {n | ∃ p q, IsPalindrome g p ∧ IsPalindrome g q ∧ p + q = n}

/--
`sumsOfTwoPositive g` is the set of numbers $p + q$ with $p, q$ positive base-`g` palindromes.
This is the convention of [Za24], where palindromes are positive.
-/
def sumsOfTwoPositive (g : ℕ) : Set ℕ :=
  {n | ∃ p q, 0 < p ∧ 0 < q ∧ IsPalindrome g p ∧ IsPalindrome g q ∧ p + q = n}

/-- $0$ is a palindrome in every base. -/
@[category test, AMS 11]
theorem isPalindrome_zero (g : ℕ) : IsPalindrome g 0 := by
  simp [IsPalindrome]

/-- $121$ is a palindrome in base $10$. -/
@[category test, AMS 11]
theorem isPalindrome_121 : IsPalindrome 10 121 := by
  unfold IsPalindrome
  rfl

/--
Are a positive proportion of positive integers a sum of two palindromes?

[Gr24] adds: "Of course one must specify a base $g$ (say $g = 10$) in which one is working." We
state the question in every base $g \ge 2$ and read "a positive proportion" as positive lower
density. Whether $0$ counts as a palindrome does not change the density.

The answer is no: Zakharov showed that the number of $n < X$ which are sums of two base-$g$
palindromes is at most $X / \log^c X$ [Za24, Theorem 1], see `green_95.variants.zakharov`.
-/
@[category research solved, question, AMS 11]
theorem green_95 : ∀ g : ℕ, 2 ≤ g → ¬ 0 < (sumsOfTwo g).lowerDensity := by
  sorry

/--
**Zakharov's theorem.** For every integer $g \ge 2$ there is a constant $c > 0$ such that, for all
large $X$, the number of $n < X$ which are a sum of two positive base-$g$ palindromes is at most
$X / \log^c X$ [Za24, Theorem 1]. We state it for integer $X$. This answers the question of
[CLB18], who had proved an upper bound $c X$ with $c < 1$ for $g \ge 3$ [CLB18, Theorem 1.4].
-/
@[category research solved, AMS 11]
theorem green_95.variants.zakharov :
    ∀ g : ℕ, 2 ≤ g → ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      ((sumsOfTwoPositive g ∩ Set.Iio X).ncard : ℝ) ≤ (X : ℝ) / Real.log X ^ c := by
  sorry

/--
**Cilleruelo, Luca and Baxter.** Let $g \ge 5$. Then every positive integer is a sum of three
base-$g$ palindromes [CLB18, Theorem 1.2]. Here $0$ counts as a palindrome, as in [CLB18], so
this says that every positive integer is a sum of at most three positive palindromes.
-/
@[category research solved, AMS 11]
theorem green_95.variants.three_palindromes :
    ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, 0 < n →
      ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p + q + r = n := by
  sorry

/--
**Cilleruelo, Luca and Baxter.** Let $g \ge 2$. There is a constant $c_1 > 0$ such that, for all
real $x \ge 2$, the number of $n \le x$ which are a sum of two base-$g$ palindromes is at least
$x^{1 - c_1 / \sqrt{\log x}} = x e^{-c_1 \sqrt{\log x}}$ [CLB18, Theorem 1.3]. We count positive
$n$ only.
-/
@[category research solved, AMS 11]
theorem green_95.variants.lower_bound :
    ∀ g : ℕ, 2 ≤ g → ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ x : ℝ, 2 ≤ x →
      x ^ (1 - c₁ / Real.sqrt (Real.log x)) ≤
        ({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ n ∈ sumsOfTwo g}.ncard : ℝ) := by
  sorry

end Green95
