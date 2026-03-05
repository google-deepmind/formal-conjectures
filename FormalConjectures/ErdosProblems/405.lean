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
# Erdős Problem 405

*Reference:* [erdosproblems.com/405](https://www.erdosproblems.com/405)

Let $p$ be an odd prime. Is it true that the equation
$(p-1)! + a^{p-1} = p^k$
has only finitely many solutions?

Erdős and Graham remark that it is probably true that in general
$(p-1)! + a^{p-1}$ is rarely a power at all (although this can happen,
for example $6! + 2^6 = 28^2$).

Brindza and Erdős [BrEr91] proved that there are finitely many solutions.
Yu and Liu [YuLi96] showed that the only solutions are
$2! + 1^2 = 3$, $2! + 5^2 = 3^3$, and $4! + 1^4 = 5^2$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[BrEr91] Brindza, B. and Erdős, P., *On some Diophantine problems involving powers and
factorials*. J. Austral. Math. Soc. Ser. A 51 (1991), 1-7.

[YuLi96] Yu, K. and Liu, L., *On some Diophantine equations involving powers and factorials*.
(1996).
-/

namespace Erdos405

/--
Erdős Problem 405 [ErGr80, p.80]:

There are only finitely many triples $(p, a, k)$ of natural numbers with $p$ an
odd prime such that $(p-1)! + a^{p-1} = p^k$.
-/
@[category research solved, AMS 11]
theorem erdos_405 : answer(True) ↔
    Set.Finite {t : ℕ × ℕ × ℕ |
      let p := t.1
      let a := t.2.1
      let k := t.2.2
      Nat.Prime p ∧ p ≠ 2 ∧ (p - 1).factorial + a ^ (p - 1) = p ^ k} := by
  sorry

end Erdos405
