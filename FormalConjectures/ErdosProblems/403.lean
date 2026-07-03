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
# Erdős Problem 403

*References:*
- [erdosproblems.com/403](https://www.erdosproblems.com/403)
- [Li76] Lin, S., *On two problems of Erdős concerning sums of distinct factorials*.
  Bell Laboratories internal memorandum (1960).
-/

namespace Erdos403

/--
Does the equation
\[2^m=a_1!+\cdots+a_k!\]
with $a_1<a_2<\cdots <a_k$ have only finitely many solutions?

Asked by Burr and Erdős. Frankl and Lin [Li76] independently showed that the answer is yes, and
the largest solution is
\[2^7=2!+3!+5!.\]
In fact Lin showed that the largest power of $2$ which can divide a sum of distinct factorials
containing $2$ is $2^{254}$, and that there are only 5 solutions to $3^m=a_1!+\cdots+a_k!$
(when $m=0,1,2,3,6$).

See also [404].

A solution is encoded below as a pair $(m, s)$ where $s$ is the finite set
$\{a_1 < a_2 < \cdots < a_k\}$ of positive integers, so the distinctness of the $a_i$ is
given by set membership. The empty set contributes no solutions since $2^m \geq 1 > 0$.
-/
@[category research solved, AMS 11]
theorem erdos_403 : answer(True) ↔
    {p : ℕ × Finset ℕ | (∀ a ∈ p.2, 0 < a) ∧
      2 ^ p.1 = ∑ a ∈ p.2, a.factorial}.Finite := by
  sorry

end Erdos403
