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

import FormalConjecturesUtil

/-!
# Erdős Problem 473

*References:*
- [erdosproblems.com/473](https://www.erdosproblems.com/473)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*, Monographies de L'Enseignement Mathématique (1980).
-/

namespace Erdos473

/--
Is there a permutation $a_1, a_2, \ldots$ of the positive integers such that $a_k + a_{k+1}$ is
always prime?

A question of Segal [ErGr80, p.94]. The answer is yes, as shown by Odlyzko. The linked formal
proof (Codex and GPT-5.6 Sol) builds the permutation as a spanning one-way ray of the graph on the
positive integers in which two numbers are adjacent when their sum is prime.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos473.lean#L236"]
theorem erdos_473 : answer(True) ↔
    ∃ a : ℕ ≃ ℕ+, ∀ n : ℕ, ((a n : ℕ) + (a (n + 1) : ℕ)).Prime := by
  sorry

/--
Segal also asked whether for every $n \ge 2$ there is a permutation $a_1, \ldots, a_n$ of
$\{1, \ldots, n\}$ such that $a_k + a_{k+1}$ is prime for all $1 \le k < n$. This is conjectured to
be true, and has been verified for infinitely many $n$.
-/
@[category research open, AMS 11]
theorem erdos_473.variants.finite : answer(sorry) ↔
    ∀ n : ℕ, 2 ≤ n → ∃ a : Fin n ≃ Fin n, ∀ k : Fin n, ∀ h : k.val + 1 < n,
      ((a k).val + 1 + ((a ⟨k.val + 1, h⟩).val + 1)).Prime := by
  sorry

end Erdos473
