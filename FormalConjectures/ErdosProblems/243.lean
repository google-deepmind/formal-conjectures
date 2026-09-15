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

import FormalConjecturesUtil

/-!
# Erdős Problem 243

*Reference:* [erdosproblems.com/243](https://www.erdosproblems.com/243)
-/

open Filter

open scoped Topology

namespace Erdos243

/--
Let $a_1 < a_2 < \dots$ be a sequence of integers such that
$\lim_{n\to\infty} \frac{a_n}{a_{n-1}^2} = 1$ and $\sum \frac{1}{a_n} \in \mathbb{Q}$.

Then, for all sufficiently large $n \ge 1$, $a_n = a_{n-1}^2 - a_{n-1} + 1$.
-/
@[category research open, AMS 40]
theorem erdos_243 (a : ℕ → ℕ) (ha₀ : StrictMono a)
    (ha₁ : Tendsto (fun n ↦ (a n : ℝ) / a (n - 1) ^ 2) atTop (𝓝 1))
    (ha₂ : Summable ((1 : ℚ) / a ·)) :
      ∀ᶠ n in atTop, a n = a (n - 1) ^ 2 - a (n - 1) + 1 := by
  sorry

/--
The denominator state of the cleared reciprocal tail: $D_0 = q$ and
$D_{n+1} = a_n D_n$.
-/
def denState (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => a n * denState q a n

/--
The tail state of the cleared reciprocal tail: $C_0 = p$ and
$C_{n+1} = a_n C_n - D_n$. When $\sum_n 1/a_n = p/q$ this is the integer
$C_n = D_n \sum_{k \ge n} 1/a_k$.
-/
def tailState (p q : ℕ) (a : ℕ → ℕ) : ℕ → ℤ
  | 0 => (p : ℤ)
  | n + 1 => (a n : ℤ) * tailState p q a n - (denState q a n : ℤ)

/--
The centred state $E_n = D_n - (a_n - 1) C_n$. It measures the deviation of the
tail from the Sylvester identity $\sum_{k \ge n} 1/a_k = 1/(a_n - 1)$, and it
vanishes at every index of Sylvester's sequence $2, 3, 7, 43, 1807, \dots$.
-/
def centredState (p q : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  (denState q a n : ℤ) - ((a n : ℤ) - 1) * tailState p q a n

/--
Let $a_n > 1$ be integers with $\sum_n 1/a_n = p/q$ rational, and let $C_n$ and
$E_n$ be the tail state and the centred state of the cleared reciprocal tail.
Assume the tail state at most doubles, $C_{n+1} < 2 C_n$; assume the negative
part of the centred state is bounded, $-B \le E_n$ for a fixed $B$; and assume
normalised vanishing, that for every $K$ one has $K |E_n| < C_n$ for all large
$n$. Then $a_n = a_{n-1}^2 - a_{n-1} + 1$ for all sufficiently large $n$.

The rationality hypotheses are used: they force $C_n = D_n \sum_{k \ge n} 1/a_k$
to be a positive integer at every index, and positivity of $C$ turns the
doubling hypothesis into the strict centring $|E_n| < C_n$ that drives the
argument.

Erdős and Straus [ES64] settle the case $E_n \ge 0$ of the problem. The theorem
here reaches the same conclusion from a bounded negative part, with no
periodicity assumption on the sign pattern of $E$. Normalised vanishing remains
a hypothesis; Koizumi [Ko25] supplies it for the canonical pseudo-greedy orbit.

This does not decide `erdos_243`. The remaining obstruction there is a centred
state with cofinally unbounded negative excursions, which the hypotheses above
exclude.

[ES64] Erdős, P. and Straus, E. G., On the irrationality of certain series,
Pacific J. Math. 14 (1964), 128-137, Theorem 3, p. 132.

[Ko25] Koizumi, J., Irrationality of the reciprocal sum of doubly exponential
sequences, [arXiv:2504.05933](https://arxiv.org/abs/2504.05933) (2025),
Lemma 15, p. 9.
-/
@[category research solved, AMS 40, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-erdos/blob/263335d19c7eff0b41b67dabbcc706f037876587/adapters/FormalConjecturesVariants.lean#L735-L870"]
theorem erdos_243.variants.bounded_negative_error
    (a : ℕ → ℕ) (p q B : ℕ)
    (ha : ∀ n, 1 < a n)
    (hq : 0 < q)
    (ha₂ : Summable ((1 : ℚ) / a ·))
    (hpq : ∑' n, (1 : ℚ) / a n = (p : ℚ) / (q : ℚ))
    (hgrow : ∀ n, tailState p q a (n + 1) < 2 * tailState p q a n)
    (hbound : ∀ n, -(B : ℤ) ≤ centredState p q a n)
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n →
      (K : ℤ) * |centredState p q a n| < tailState p q a n) :
    ∀ᶠ n in atTop, a n = a (n - 1) ^ 2 - a (n - 1) + 1 := by
  sorry

end Erdos243
