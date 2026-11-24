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
# Erdős Problem 383

*Reference:* [erdosproblems.com/383](https://www.erdosproblems.com/383)
-/

@[expose] public section

namespace Erdos383

/--
Is it true that for every $k$ there are infinitely many primes $p$ such that the largest prime
divisor of
$$
  \prod_{i = 0}^k (p ^ 2 + i)
$$
is $p$?
-/
@[category research open, question, AMS 11]
theorem erdos_383 :
    ∀ k, {p : ℕ | p.Prime ∧ Nat.maxPrimeFac (∏ i ∈ Finset.Icc 0 k, (p ^ 2 + i)) = p}.Infinite := by
  sorry

set_option linter.style.formal_proof_palomar false in
/--
For $k = 13$ there is at least one prime $p$ such that the largest prime divisor of
$\prod_{i = 0}^{13} (p ^ 2 + i)$ is $p$, namely $p = 169638367$. This is a single witness and says
nothing about the infinitude asked for in `erdos_383`. Earlier witnesses: on the erdosproblems.com
forum, Kitamura (June 2026) gave $p = 9188057$ for $k = 10$, and Zeraoulia (proof-claims tab and
Zenodo record 21544693, July 2026) gave $p = 93609881$ for $k = 12$ and reported that no
$p \leq 10^8$ works for $k = 13$.

The proof checks that $p$ is prime and writes each $p ^ 2 + i$, $1 \leq i \leq 13$, as an explicit
product of integers less than $p$. A prime dividing $p ^ 2 + i$ divides one of these integers, so
it is less than $p$, while the factor $p ^ 2$ makes $p$ itself a prime divisor of the product.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/mnn31/erdos-lean/blob/521f9e87e9416a8043365d7b84279d1389850a2e/ErdosLean/Erdos383K13.lean#L74-L88"]
theorem erdos_383.variants.k_eq_13 :
    {p : ℕ | p.Prime ∧ Nat.maxPrimeFac (∏ i ∈ Finset.Icc 0 13, (p ^ 2 + i)) = p}.Nonempty := by
  sorry

end Erdos383
