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
# Erdős Problem 334

*Reference:* [erdosproblems.com/334](https://www.erdosproblems.com/334)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

[Er82d] Erdős, P., _Problems and results in number theory_. In: Recent progress in analytic
number theory, Vol. 1 (Durham, 1979), Academic Press, London-New York (1981), 1-13.

[Ba89] Balog, A., _On the distribution of integers having no large prime factor_. Astérisque
(1989).
-/

namespace Erdos334

/-- A natural number is $B$-smooth if all its prime factors are at most $B$. -/
def IsSmooth (B n : ℕ) : Prop := ∀ p ∈ n.primeFactorsList, p ≤ B

/--
Erdős Problem 334 [ErGr80, p.70] [Er82d, p.55]:

Find the best function $f(n)$ such that every $n$ can be written as $n = a + b$
where both $a$, $b$ are $f(n)$-smooth (not divisible by any prime $p > f(n)$).

Erdős originally asked if $f(n) \leq n^{1/3}$. Balog [Ba89] proved
$f(n) \ll_\varepsilon n^{4/(9\sqrt{e}) + \varepsilon}$ for all $\varepsilon > 0$.
It is conjectured that $f(n) \leq n^{o(1)}$, or even $f(n) \leq e^{O(\sqrt{\log n})}$.

We formalize the conjecture that $f(n) = n^{o(1)}$: for every $\varepsilon > 0$,
for sufficiently large $n$, $n$ can be written as a sum of two
$\lfloor n^\varepsilon \rfloor$-smooth numbers.
-/
@[category research open, AMS 11]
theorem erdos_334 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ a b : ℕ, a + b = n ∧
          IsSmooth (⌊(n : ℝ) ^ ε⌋₊) a ∧
          IsSmooth (⌊(n : ℝ) ^ ε⌋₊) b := by
  sorry

end Erdos334
