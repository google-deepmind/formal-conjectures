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
# Erdős Problem 407

*Reference:* [erdosproblems.com/407](https://www.erdosproblems.com/407)

Let $w(n)$ count the number of solutions to $n = 2^a + 3^b + 2^c \cdot 3^d$ with
$a, b, c, d \geq 0$ integers. Is it true that $w(n)$ is bounded by some absolute
constant?

A conjecture originally due to Newman. This was proved by Evertse, Györy,
Stewart, and Tijdeman [EGST88]. Tijdeman and Wang [TiWa88] showed that
$w(n) \leq 4$ for all large $n$. Bajpai and Bennett [BaBe24] showed that
$w(n) \leq 4$ for $n \geq 131082$ and $w(n) \leq 9$ for all $n$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in
combinatorial number theory*. Monographies de L'Enseignement Mathematique (1980).

[EGST88] Evertse, J.-H., Györy, K., Stewart, C. L., and Tijdeman, R.,
*S-unit equations and their applications*. New advances in transcendence theory
(Durham, 1986), Cambridge Univ. Press (1988), 110-174.

[TiWa88] Tijdeman, R. and Wang, L. X., *Sums of products of powers of given prime
numbers*. Pacific Journal of Mathematics (1988), 177-193.

[BaBe24] Bajpai, P. and Bennett, M. A., *Effective S-unit equations beyond three
terms: Newman's conjecture*. Acta Arithmetica (2024), 421-458.
-/

namespace Erdos407

/--
Erdős Problem 407 [ErGr80, p.80]:

There exists an absolute constant $C$ such that for every natural number $n$,
the number of 4-tuples $(a, b, c, d)$ of natural numbers satisfying
$n = 2^a + 3^b + 2^c \cdot 3^d$ is at most $C$.
-/
@[category research solved, AMS 11]
theorem erdos_407 : answer(True) ↔
    ∃ C : ℕ, ∀ (n : ℕ) (S : Finset (ℕ × ℕ × ℕ × ℕ)),
      (∀ t ∈ S, n = 2 ^ t.1 + 3 ^ t.2.1 + 2 ^ t.2.2.1 * 3 ^ t.2.2.2) →
      S.card ≤ C := by
  sorry

end Erdos407
