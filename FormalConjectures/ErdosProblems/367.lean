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
# Erdős Problem 367

Is it true that the product of the 2-full parts of $k$ consecutive integers starting at $n$ is
$O(n^{2+\varepsilon})$ for every fixed $k \geq 1$ and $\varepsilon > 0$?

This problem is equivalent (up to constants) to Problem 935, though the two formalizations capture
different mathematical quantities: Problem 367 computes the product of the 2-full parts of each
individual consecutive integer, while Problem 935 computes the 2-full part of the product.

*Reference:* [erdosproblems.com/367](https://www.erdosproblems.com/367)

*See also:* [Problem 935](https://www.erdosproblems.com/935),
[OEIS A057521](https://oeis.org/A057521)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators Real

namespace Erdos367

/-- The 2-full part of a natural number $n$: the product of all prime power
factors $p^a$ where $a \geq 2$. Equivalently, $B_2(n) = n/n'$ where $n'$ is the
product of all primes dividing $n$ exactly once. -/
noncomputable def twoFullPart (n : ℕ) : ℕ :=
  (n.factorization.support.filter (fun p => 2 ≤ n.factorization p)).prod
    (fun p => p ^ n.factorization p)

/--
Erdős Problem 367 [ErGr80, p.68]:

Let $B_2(n)$ be the 2-full part of $n$ (the product of prime power factors $p^a$
with $a \geq 2$). Is it true that for every fixed $k \geq 1$,
$$\prod_{n \leq m < n+k} B_2(m) \ll n^{2+o(1)}?$$

Equivalently: for every $k \geq 1$ and $\varepsilon > 0$, the product is
$O_{k,\varepsilon}(n^{2+\varepsilon})$.

van Doorn notes that the stronger bound $\ll_k n^2$ holds trivially for $k \leq 2$
but fails for all $k \geq 3$ (in fact the product is $\gg n^2 \log n$ infinitely often
when $k = 3$).
-/
@[category research open, AMS 11]
theorem erdos_367 :
    answer(sorry) ↔
    ∀ k : ℕ, 1 ≤ k →
    ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ((∏ i ∈ Finset.range k, twoFullPart (n + i) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ (2 + ε) := by
  sorry

/-- The r-full part of a natural number $n$: the product of all prime power
factors $p^a$ where $a \geq r$. When $r = 2$, this is `twoFullPart`. -/
noncomputable def rFullPart (r : ℕ) (n : ℕ) : ℕ :=
  (n.factorization.support.filter (fun p => r ≤ n.factorization p)).prod
    (fun p => p ^ n.factorization p)

/--
Erdős Problem 367, r-full variant:

The website asks whether, for fixed $r, k \geq 2$ and $\varepsilon > 0$,
$$\limsup_{n \to \infty} \frac{\prod_{n \leq m < n+k} B_r(m)}{n^{1+\varepsilon}} = \infty,$$
i.e., the product of $r$-full parts of $k$ consecutive integers grows faster than
$n^{1+\varepsilon}$ for any $\varepsilon > 0$.
-/
@[category research open, AMS 11]
theorem erdos_367_rFull :
    answer(sorry) ↔
    ∀ r : ℕ, 2 ≤ r →
    ∀ k : ℕ, 2 ≤ k →
    ∀ ε : ℝ, 0 < ε →
    ∀ C : ℝ, ∃ n : ℕ,
      C * (n : ℝ) ^ (1 + ε) ≤
        ((∏ i ∈ Finset.range k, rFullPart r (n + i) : ℕ) : ℝ) := by
  sorry

end Erdos367
