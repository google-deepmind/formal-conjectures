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
# Erdős Problem 487

*References:*
- [erdosproblems.com/487](https://www.erdosproblems.com/487)
- [Er61] Erdős, Paul, *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221-254.
- [Er65b] Erdős, Paul, *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [DaEr36] Davenport, H. and Erdős, P., *On sequences of positive integers*. Acta Arithmetica
  (1936), 147-151.
- [Kl71] Kleitman, Daniel, *Collections of subsets containing no two sets and their union*.
  Proceedings of the LA Meeting AMS (1971), 153-155.
-/

namespace Erdos487

/--
Let $A\subseteq \mathbb{N}$ have positive density. Must there exist distinct $a,b,c\in A$ such
that $[a,b]=c$ (where $[a,b]$ is the least common multiple of $a$ and $b$)?

This is true, a consequence of the positive solution to [447] by Kleitman [Kl71].

Davenport and Erdős [DaEr36] showed that there must exist an infinite sequence $a_1<a_2\cdots$
in $A$ such that $a_i\mid a_j$ for all $i\leq j$, under the assumption that the upper logarithmic
density of $A$ is positive.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos487.lean"]
theorem erdos_487 : answer(True) ↔
    ∀ A : Set ℕ, A.HasPosDensity →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Nat.lcm a b = c := by
  sorry

end Erdos487
