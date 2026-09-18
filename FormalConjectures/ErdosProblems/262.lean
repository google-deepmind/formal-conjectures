/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 262

*References:*
- [erdosproblems.com/262](https://www.erdosproblems.com/262)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Er88c] Erdős, P., *On the irrationality of certain series: problems and results*. New advances
  in transcendence theory (Durham, 1986) (1988), 102-109.
- [Er75c] Erdős, P., *Some problems and results on the irrationality of the sum of infinite
  series*. J. Math. Sci. (1975), 1-7 (1976).
- [Ha91] Hančl, Jaroslav, *Expression of real numbers with the help of infinite series*. Acta
  Arith. (1991), 97--104.
-/

@[expose] public section

open Filter

namespace Erdos262

/-- A strictly increasing sequence $a_1 < a_2 < \cdots$ of positive integers is an irrationality
sequence if $\sum_n \frac{1}{t_n a_n}$ is irrational for every sequence of positive integers
$t_n$. -/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ StrictMono a ∧
    ∀ t : ℕ → ℕ, (∀ n, 0 < t n) → Irrational (∑' n, 1 / ((t n : ℝ) * a n))

/--
Suppose $a_1<a_2<\cdots$ is a sequence of integers such that for all integer sequences $t_n$
with $t_n\geq 1$ the sum
$$\sum_{n=1}^\infty \frac{1}{t_na_n}$$
is irrational. How slowly can $a_n$ grow?

One possible definition of an 'irrationality sequence' (see also
[263](https://www.erdosproblems.com/263) and [264](https://www.erdosproblems.com/264)). An
example of such a sequence is $a_n=2^{2^n}$ (proved by Erdős [Er75c]), while a non-example is
$a_n=n!$. It is known that if $a_n$ is such a sequence then $a_n^{1/n}\to\infty$.

This was essentially solved by Hančl [Ha91], who proved that such a sequence needs to satisfy
$$\limsup_{n\to \infty} \frac{\log_2\log_2 a_n}{n} \geq 1.$$
More generally, if $a_n\ll 2^{2^{n-F(n)}}$ with $F(n)<n$ and $\sum 2^{-F(n)}<\infty$ then $a_n$
cannot be an irrationality sequence.

The sequence is indexed from $0$, so `a n` is $a_{n+1}$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos262.lean#L455"]
theorem erdos_262 (a : ℕ → ℕ) (ha : IsIrrationalitySequence a) :
    (1 : EReal) ≤ atTop.limsup fun n : ℕ =>
      ((Real.logb 2 (Real.logb 2 (a n)) / (n + 1) : ℝ) : EReal) := by
  sorry

/--
If $a_n\ll 2^{2^{n-F(n)}}$ with $F(n)<n$ and $\sum 2^{-F(n)}<\infty$ then $a_n$ cannot be an
irrationality sequence [Ha91].
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos262.lean#L361"]
theorem erdos_262.variants.general_growth (a : ℕ → ℕ) (F : ℕ → ℝ) (hF : ∀ n, F n < n + 1)
    (hsum : Summable fun n => (2 : ℝ) ^ (-F n))
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (a n : ℝ) ≤ C * 2 ^ (2 : ℝ) ^ (n + 1 - F n)) :
    ¬ IsIrrationalitySequence a := by
  sorry

/-- The sequence $a_n=2^{2^n}$ is an irrationality sequence (Erdős [Er75c]). -/
@[category research solved, AMS 11]
theorem erdos_262.variants.two_pow_two_pow :
    IsIrrationalitySequence fun n => 2 ^ 2 ^ (n + 1) := by
  sorry

/-- The sequence $a_n=n!$ is not an irrationality sequence. -/
@[category research solved, AMS 11]
theorem erdos_262.variants.factorial : ¬ IsIrrationalitySequence fun n => (n + 1).factorial := by
  sorry

end Erdos262
