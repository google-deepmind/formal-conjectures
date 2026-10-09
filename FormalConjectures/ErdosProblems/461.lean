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
# Erdős Problem 461

*References:*
- [erdosproblems.com/461](https://www.erdosproblems.com/461)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
-/

@[expose] public section

namespace Erdos461

/-- The $t$-smooth component $s_t(n)$ of $n$: the product of all primes $p < t$ dividing $n$,
counted with multiplicity. -/
def smoothComponent (t n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (· < t)).prod

/-- The number $f(n,t)$ of distinct values of $s_t(m)$ for $m \in [n+1, n+t]$. -/
def f (n t : ℕ) : ℕ :=
  ((Finset.Icc (n + 1) (n + t)).image (smoothComponent t)).card

/--
Let $s_t(n)$ be the $t$-smooth component of $n$ - that is, the product of all primes $p$ (with
multiplicity) dividing $n$ such that $p<t$. Let $f(n,t)$ count the number of distinct possible
values for $s_t(m)$ for $m\in [n+1,n+t]$. Is it true that
$$f(n,t)\gg t$$
(uniformly, for all $t$ and $n$)?

Erdős and Graham report they can show
$$f(n,t) \gg \frac{t}{\log t}.$$
-/
@[category research open, AMS 11]
theorem erdos_461 : answer(sorry) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ n t : ℕ, 1 ≤ t → c * (t : ℝ) ≤ (f n t : ℝ) := by
  sorry

/-- The $t$-smooth component is $t$-smooth in the sense of `Nat.smoothNumbers`. -/
@[category API, AMS 11]
theorem smoothComponent_mem_smoothNumbers (t n : ℕ) : smoothComponent t n ∈ Nat.smoothNumbers t :=
  Nat.prod_mem_smoothNumbers n t

/-- Multiplicity counts: $s_t(p^k) = p^k$ if $p < t$, and $s_t(p^k) = 1$ if $p \geq t$. -/
@[category test, AMS 11]
theorem smoothComponent_prime_pow {p : ℕ} (hp : p.Prime) (k t : ℕ) :
    smoothComponent t (p ^ k) = if p < t then p ^ k else 1 := by
  by_cases h : p < t <;> simp [smoothComponent, hp.primeFactorsList_pow, h]

/-- For $t = 1$ the interval $[n+1, n+1]$ has one element, so $f(n,1) = 1$. -/
@[category test, AMS 11]
theorem f_one (n : ℕ) : f n 1 = 1 := by
  simp only [f, Finset.Icc_self, Finset.image_singleton, Finset.card_singleton]

end Erdos461
