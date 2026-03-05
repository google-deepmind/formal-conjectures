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
# Erdős Problem 937

*Reference:* [erdosproblems.com/937](https://www.erdosproblems.com/937)

Are there infinitely many four-term arithmetic progressions of coprime powerful
numbers (i.e. if $p \mid n$ then $p^2 \mid n$)?

This was proved in the affirmative by Bajpai, Bennett, and Chan [BBC24].

[BBC24] Bajpai, P., Bennett, M.A., and Chan, T.H., *Arithmetic progressions of
powerful numbers*, 2024.
-/

namespace Erdos937

/-- A natural number $n$ is powerful (also called 2-full) if for every prime $p$
dividing $n$, $p^2$ also divides $n$. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Erdős Problem 937 (proved by Bajpai–Bennett–Chan [BBC24]):

There are infinitely many four-term arithmetic progressions of pairwise coprime
powerful numbers. Formulated as: for every $N$, there exist $a > 0$, $d > 0$ with
$a \geq N$ such that $a$, $a+d$, $a+2d$, $a+3d$ are all powerful and pairwise coprime.
-/
@[category research solved, AMS 11]
theorem erdos_937 :
    answer(True) ↔
      ∀ N : ℕ, ∃ a d : ℕ, N ≤ a ∧ 0 < a ∧ 0 < d ∧
        IsPowerful a ∧ IsPowerful (a + d) ∧
        IsPowerful (a + 2 * d) ∧ IsPowerful (a + 3 * d) ∧
        Nat.Coprime a (a + d) ∧
        Nat.Coprime a (a + 2 * d) ∧
        Nat.Coprime a (a + 3 * d) ∧
        Nat.Coprime (a + d) (a + 2 * d) ∧
        Nat.Coprime (a + d) (a + 3 * d) ∧
        Nat.Coprime (a + 2 * d) (a + 3 * d) := by
  sorry

end Erdos937
