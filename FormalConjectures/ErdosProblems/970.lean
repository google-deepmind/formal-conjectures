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
# Erdős Problem 970

*Reference:* [erdosproblems.com/970](https://www.erdosproblems.com/970)

Let $h(k)$ be Jacobsthal's function, defined as the minimal $m$ such that,
if $n$ has at most $k$ prime factors, then in any set of $m$ consecutive
integers there exists an integer coprime to $n$. Is it true that $h(k) \ll k^2$?

This is Jacobsthal's conjecture. Iwaniec [Iw78] proved $h(k) \ll (k \log k)^2$.
The best known lower bound is
$h(k) \gg k \cdot (\log k)(\log \log \log k)/(\log \log k)^2$,
due to Ford, Green, Konyagin, Maynard, and Tao [FGKMT18].

This is a more general form of the function considered in problem 687.

[Er65b] Erdős, P., *Extremal problems in number theory*.

[Iw78] Iwaniec, H., *On the problem of Jacobsthal*.

[FGKMT18] Ford, B., Green, B., Konyagin, S., Maynard, J., and Tao, T.,
*Long gaps between primes*.
-/

namespace Erdos970

/-- Jacobsthal's function $h(k)$: the smallest $m$ such that for every positive
    integer $n$ with at most $k$ distinct prime factors, among any $m$ consecutive
    natural numbers there is one coprime to $n$. -/
noncomputable def jacobsthal (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℕ, ∃ i : ℕ, i < m ∧ Nat.Coprime (a + i) n}

/--
Erdős Problem 970 (Jacobsthal's conjecture) [Er65b]:

Is it true that $h(k) \ll k^2$, i.e., there exists a constant $C > 0$ such that
$h(k) \le C \cdot k^2$ for all $k$?
-/
@[category research open, AMS 11]
theorem erdos_970 :
    answer(sorry) ↔
      ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, (jacobsthal k : ℝ) ≤ C * (k : ℝ) ^ 2 := by
  sorry

end Erdos970
