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
# Erdős Problem 473

*Reference:* [erdosproblems.com/473](https://www.erdosproblems.com/473)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).

Is there a permutation $a_1, a_2, \ldots$ of the positive integers such that $a_k + a_{k+1}$ is
always prime? Asked by Segal. The answer is yes, as shown by Odlyzko.

See also OEIS sequence [A055265](https://oeis.org/A055265).
-/

namespace Erdos473

/--
Erdős Problem 473 (Segal):
There exists a permutation $a_1, a_2, \ldots$ of the positive integers such that
$a_k + a_{k+1}$ is prime for all $k$. The answer is yes, as shown by Odlyzko.

The function $a : \mathbb{N} \to \mathbb{N}$ represents the sequence (0-indexed), and the three
conditions (injective, values positive, surjective onto positives) together
encode that $a$ is a bijection from $\mathbb{N}$ onto the positive integers.
-/
@[category research solved, AMS 5 11]
theorem erdos_473 :
    answer(True) ↔
    ∃ a : ℕ → ℕ, Function.Injective a ∧
    (∀ n, 0 < a n) ∧
    (∀ m, 0 < m → ∃ n, a n = m) ∧
    ∀ k, Nat.Prime (a k + a (k + 1)) := by
  sorry

end Erdos473
