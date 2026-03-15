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
import FormalConjecturesForMathlib.Data.Nat.Full

/-!
# Erdős Problem 937

*Reference:* [erdosproblems.com/937](https://www.erdosproblems.com/937)

Are there infinitely many four-term arithmetic progressions of coprime powerful
numbers (i.e. if $p \mid n$ then $p^2 \mid n$)?

This was proved in the affirmative by Bajpai, Bennett, and Chan [BBC24].

[Er76d] Erdős, P., _Problems and results on number theoretic properties of consecutive
integers and related questions_. Proceedings of the Fifth Manitoba Conference on
Numerical Mathematics (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25–44.

[BBC24] Bajpai, P., Bennett, M.A., and Chan, T.H., _Arithmetic progressions in
squarefull numbers_. Int. J. Number Theory (2024), 19–45.
-/

open Nat

namespace Erdos937

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
        a.Powerful ∧ (a + d).Powerful ∧
        (a + 2 * d).Powerful ∧ (a + 3 * d).Powerful ∧
        Nat.Coprime a (a + d) ∧
        Nat.Coprime a (a + 2 * d) ∧
        Nat.Coprime a (a + 3 * d) ∧
        Nat.Coprime (a + d) (a + 2 * d) ∧
        Nat.Coprime (a + d) (a + 3 * d) ∧
        Nat.Coprime (a + 2 * d) (a + 3 * d) := by
  sorry

/--
Variant (proved by Bajpai–Bennett–Chan [BBC24]):

There are infinitely many three-term arithmetic progressions of pairwise coprime
3-powerful numbers (i.e. if $p \mid n$ then $p^3 \mid n$).
-/
@[category research solved, AMS 11]
theorem erdos_937_three_powerful_three_term :
    answer(True) ↔
      ∀ N : ℕ, ∃ a d : ℕ, N ≤ a ∧ 0 < a ∧ 0 < d ∧
        Full 3 a ∧ Full 3 (a + d) ∧ Full 3 (a + 2 * d) ∧
        Nat.Coprime a (a + d) ∧
        Nat.Coprime a (a + 2 * d) ∧
        Nat.Coprime (a + d) (a + 2 * d) := by
  sorry

/--
Variant (Erdős conjecture [Er76d], proved conditionally on the ABC conjecture by
Bajpai–Bennett–Chan [BBC24]):

For $r \geq 4$, there are only finitely many three-term arithmetic progressions of
pairwise coprime $r$-powerful numbers.
-/
@[category research open, AMS 11]
theorem erdos_937_r_powerful_three_term :
    answer(sorry) ↔
      ∀ r : ℕ, 4 ≤ r →
      {x : ℕ × ℕ | 0 < x.1 ∧ 0 < x.2 ∧
        Full r x.1 ∧ Full r (x.1 + x.2) ∧ Full r (x.1 + 2 * x.2) ∧
        Nat.Coprime x.1 (x.1 + x.2) ∧
        Nat.Coprime x.1 (x.1 + 2 * x.2) ∧
        Nat.Coprime (x.1 + x.2) (x.1 + 2 * x.2)}.Finite := by
  sorry

end Erdos937
