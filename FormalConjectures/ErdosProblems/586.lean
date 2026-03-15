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
# Erdős Problem 586

*Reference:* [erdosproblems.com/586](https://www.erdosproblems.com/586)

Asked by Schinzel, motivated by a question of Erdős and Selfridge.
The answer is no, as proved by Balister, Bollobás, Morris, Sahasrabudhe,
and Tiba [BBMST22]. Selfridge showed that a positive answer to this problem
would imply a positive answer to Problem 7 (odd covering systems).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathématique (1980).

[Er96b] Erdős, P., _Some problems I presented or planned to present in my short talk_.
Analytic number theory, Vol. 1 (Allerton Park, IL, 1995) (1996), 333–335.

[Er97] Erdős, P., _Some of my new and almost new problems and results in combinatorial
number theory_ (1997).

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.

[Er97e] Erdős, P., _Some problems and results on combinatorial number theory_ (1997).

[BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and Tiba, M.,
_On the Erdős covering problem: the density of the uncovered set_, Inventiones
mathematicae (2022).
-/

namespace Erdos586

/-- A covering system: a finite collection of residue classes $a_i \bmod n_i$ (with $n_i \geq 2$)
    that covers every integer. -/
def IsCoveringSystem (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ) : Prop :=
  (∀ i : Fin k, 2 ≤ n i) ∧
  (∀ z : ℤ, ∃ i : Fin k, (n i : ℤ) ∣ (z - a i))

/-- **Erdős Problem 586** (Schinzel): Is there a covering system such that no two of the
    moduli divide each other? The answer is no, as proved by Balister, Bollobás, Morris,
    Sahasrabudhe, and Tiba [BBMST22]. -/
@[category research solved, AMS 11]
theorem erdos_586 : answer(False) ↔
    (∃ (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ),
      IsCoveringSystem k a n ∧
      ∀ i j : Fin k, i ≠ j → ¬(n i ∣ n j)) := by
  sorry

end Erdos586
