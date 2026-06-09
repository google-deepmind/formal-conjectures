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

Are there infinitely many four-term arithmetic progressions of coprime powerful numbers?
(A number `n` is *powerful* if `p ∣ n → p² ∣ n`; `Nat.Powerful`.)

Erdős [Er76d] asked this; Bajpai, Bennett and Chan [BBC24] proved the answer is **yes** —
there are infinitely many four-term arithmetic progressions of pairwise coprime powerful numbers.
(Note: without coprimality this is easy, and by a theorem of Fermat there are no four *squares*
in arithmetic progression.)

[BBC24] Bajpai, P., Bennett, M. A. and Chan, T. H., _Arithmetic progressions in squarefull /
powerful numbers_, Int. J. Number Theory 20 (2024), 19-45.
-/

namespace Erdos937

open Nat

/-- The four numbers `a, a+d, a+2d, a+3d` form a four-term arithmetic progression (`d > 0`) of
pairwise coprime powerful numbers. -/
def IsCoprimePowerfulAP4 (a d : ℕ) : Prop :=
  0 < d ∧
  a.Powerful ∧ (a + d).Powerful ∧ (a + 2 * d).Powerful ∧ (a + 3 * d).Powerful ∧
  a.Coprime (a + d) ∧ a.Coprime (a + 2 * d) ∧ a.Coprime (a + 3 * d) ∧
  (a + d).Coprime (a + 2 * d) ∧ (a + d).Coprime (a + 3 * d) ∧ (a + 2 * d).Coprime (a + 3 * d)

/--
Are there infinitely many four-term arithmetic progressions of coprime powerful numbers?

The answer is **yes**: Bajpai, Bennett and Chan [BBC24] proved that there are infinitely many
four-term arithmetic progressions of pairwise coprime powerful numbers.
-/
@[category research solved, AMS 11]
theorem erdos_937 :
    answer(True) ↔ {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite := by
  sorry

end Erdos937
