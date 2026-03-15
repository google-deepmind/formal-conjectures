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
# Erdős Problem 7

*Reference:* [erdosproblems.com/7](https://www.erdosproblems.com/7)

Erdős asked whether there exists a distinct covering system all of whose moduli are odd.

[HoNi19] Hough, R. D. and Nielsen, P. P., _Covering systems with restricted divisibility_.
Duke Math. J. **168** (2019), 3261–3295.

[BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and Tiba, M.,
_On the Erdős covering problem: the density of the uncovered set_. Inventiones
mathematicae (2022), 377–414.
-/

namespace Erdos7

/--
A finite system of congruences $\{(a_i, m_i)\}$ is a **covering system** if every
modulus is positive and every integer satisfies at least one congruence $n \equiv a_i \pmod{m_i}$.
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, 0 < p.2) ∧
  (∀ n : ℤ, ∃ p ∈ S, (p.2 : ℤ) ∣ (n - p.1))

/--
A covering system has **distinct moduli** if no two congruences share the same modulus.
-/
def HasDistinctModuli (S : Finset (ℤ × ℕ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q

/--
Is there a distinct covering system all of whose moduli are odd?

A **distinct covering system** is a finite collection of congruences
$\{n \equiv a_i \pmod{m_i}\}$ where all moduli $m_i$ are pairwise distinct,
covering every integer. The question asks whether such a system can exist with all
moduli odd.

Known results:
- [HoNi19] proved that in any distinct covering system, at least one modulus must be
  divisible by 2 or 3. A simpler proof was given by [BBMST22], who also showed that the
  lcm of any odd covering system's moduli must be divisible by 9 or 15.
- [BBMST22] proved no odd distinct covering system exists if the moduli are additionally
  required to be squarefree. The general odd case remains open.
-/
@[category research open, AMS 11]
theorem erdos_7 : answer(sorry) ↔
    ∃ S : Finset (ℤ × ℕ), IsCoveringSystem S ∧ HasDistinctModuli S ∧ ∀ p ∈ S, Odd p.2 := by
  sorry

end Erdos7
