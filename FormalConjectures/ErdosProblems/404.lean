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
# Erdős Problem 404

*Reference:* [erdosproblems.com/404](https://www.erdosproblems.com/404)

For which integers $a \geq 1$ and primes $p$ is there a finite upper bound on those $k$
such that there are $a = a_1 < \cdots < a_n$ with $p^k \mid (a_1! + \cdots + a_n!)$? If $f(a,p)$
is the greatest such $k$, how does this function behave?

Is there a prime $p$ and an infinite sequence $a_1 < a_2 < \cdots$ such that if $p^{m_k}$
is the highest power of $p$ dividing $\sum_{i \leq k} a_i!$ then $m_k \to \infty$?

See also Problem 403. Lin [Li76] has shown that $f(2,2) \leq 254$.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[Li76] Lin, S., _Computer experiments on sequences which form integral bases_ (1976).
-/

open Filter

open scoped BigOperators

namespace Erdos404

/--
Erdős Problem 404, Part 1 [ErGr80, p.79]:

For all integers $a \geq 1$ and all primes $p$, there is a finite upper bound on the
$p$-adic valuation of sums $a_1! + \cdots + a_n!$ over all finite sets $\{a_1, \ldots, a_n\}$ with
$a$ as the minimum element.

Formally: for every $a \geq 1$ and every prime $p$, there exists $K$ such that for every
finite set $S$ of natural numbers with $a \in S$ and $a \leq x$ for all $x \in S$, we have
$v_p\!\left(\sum_{i \in S} i!\right) \leq K$.
-/
@[category research open, AMS 11]
theorem erdos_404 (a : ℕ) (ha : 1 ≤ a) (p : ℕ) (hp : Nat.Prime p) :
    ∃ K : ℕ, ∀ S : Finset ℕ, a ∈ S → (∀ x ∈ S, a ≤ x) →
      padicValNat p (∑ i ∈ S, i.factorial) ≤ K := by
  sorry

/--
Erdős Problem 404, Part 2 [ErGr80, p.79]:

Is there a prime $p$ and strictly increasing sequence $a_1 < a_2 < \cdots$ of natural
numbers such that the $p$-adic valuation of the partial sums $\sum_{i \leq k} a_i!$ tends
to infinity?

This is expected to be a consequence of Part 1: if $f(a,p)$ is always finite, then for any
sequence starting at $a_1$, the $p$-adic valuation of partial sums is bounded by
$f(a_1, p)$.
-/
@[category research open, AMS 11]
theorem erdos_404.variants.divergence : answer(sorry) ↔
    ∃ (p : ℕ) (_ : Nat.Prime p) (a : ℕ → ℕ), StrictMono a ∧
      Tendsto (fun k => padicValNat p (∑ i ∈ Finset.range (k + 1), (a i).factorial))
        atTop atTop := by
  sorry

end Erdos404
