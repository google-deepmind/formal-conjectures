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
# Erdős Problem 1113

*References:*
- [erdosproblems.com/1113](https://www.erdosproblems.com/1113)
- [ErGr80] Erdős, P. and Graham, R. L., Old and New Problems and Results in Combinatorial
  Number Theory. Monographie de l'Enseignement Mathématique, No. 28 (1980).
- [Si60] Sierpiński, W., Elementary Theory of Numbers. Państwowe Wydawnictwo Naukowe,
  Warsaw (1960).
- [FFK08] Filaseta, M., Finch, C., and Kozek, M., On powers associated with Sierpiński numbers,
  Riesel numbers and Polignac's conjecture. Journal of Number Theory 128 (2008), 1916–1940.

Sierpiński (1960) proved that infinitely many Sierpiński numbers exist using covering systems.
The smallest known Sierpiński number is 78557 (Selfridge). Erdős and Graham conjectured that
there exist Sierpiński numbers with no finite covering set. A negative answer would imply
infinitely many Fermat primes.
-/

namespace Erdos1113

/--
A positive odd integer $m$ is a *Sierpiński number* if $2^k m + 1$ is composite for all $k \geq 0$.
-/
def IsSierpinskiNumber (m : ℕ) : Prop :=
  0 < m ∧ ¬ 2 ∣ m ∧ ∀ k, ¬ (2 ^ k * m + 1).Prime

/--
A *covering set* for a positive odd integer $m$ is a finite set of primes $P$ such that every
number of the form $2^k m + 1$ is divisible by at least one prime in $P$.
-/
def HasFinitePrimeCoveringSet (m : ℕ) : Prop :=
  ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ ∀ k, ∃ p ∈ P, p ∣ (2 ^ k * m + 1)

/--
Sierpiński [Si60] proved that there are infinitely many Sierpiński numbers, using covering
systems to construct suitable covering sets for any $m$ satisfying a certain congruence.
-/
@[category research solved, AMS 11]
theorem erdos_1113.variants.infinitely_many_sierpinski :
    Set.Infinite {m | IsSierpinskiNumber m} := by
  sorry

/--
**Erdős Problem 1113.** Do there exist Sierpiński numbers that possess no finite covering set
of primes?

Erdős and Graham [ErGr80] conjectured that the answer is yes. A negative answer would imply
that there are infinitely many Fermat primes.
-/
@[category research open, AMS 11]
theorem erdos_1113 :
    answer(sorry) ↔
      ∃ m, IsSierpinskiNumber m ∧ ¬ HasFinitePrimeCoveringSet m := by
  sorry

/--
**Filaseta–Finch–Kozek conjecture (2008).** Every Sierpiński number is either a perfect power
or possesses a finite covering set of primes.
-/
@[category research open, AMS 11]
theorem erdos_1113.variants.filaseta_finch_kozek :
    ∀ m, IsSierpinskiNumber m →
      m.IsPerfectPower ∨ HasFinitePrimeCoveringSet m := by
  sorry

end Erdos1113
