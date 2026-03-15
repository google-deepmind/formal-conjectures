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
# Erdős Problem 240

*Reference:* [erdosproblems.com/240](https://www.erdosproblems.com/240)

Is there an infinite set of primes $P$ such that if $\{a_1 < a_2 < \cdots\}$ is the set of
positive integers divisible only by primes in $P$, then $\lim(a_{i+1} - a_i) = \infty$?

Originally asked to Erdős by Wintner. The answer is yes for finite sets of primes,
which follows from a theorem of Pólya [Po18].

Tijdeman [Ti73] resolved this question, proving that for any $\varepsilon > 0$, there exists
an infinite set of primes $P$ such that $a_{i+1} - a_i \gg a_i^{1-\varepsilon}$.

See also: Problem 368.

[Er61,p.226] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
**6** (1961), 221–254.

[Er65b] Erdős, P., _Extremal problems in number theory_. Proc. Sympos. Pure Math. **8** (1965),
221–232.

[Po18] Pólya, G., _Zur arithmetischen Untersuchung der Polynome_. Math. Z. (1918), 143–148.

[Ti73] Tijdeman, R., _On integers with many small prime factors_. Compositio Math. (1973),
319–330.
-/

namespace Erdos240

/-- The set of positive integers all of whose prime factors lie in $P$. -/
def smoothNumbers (P : Set ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ ∀ q : ℕ, Nat.Prime q → q ∣ n → q ∈ P}

/--
Erdős Problem 240 [Er61,p.226][Er65b]:
There exists an infinite set of primes $P$ such that if $\{a_1 < a_2 < \cdots\}$ is the
set of positive integers divisible only by primes in $P$ (the $P$-smooth numbers),
then the consecutive gaps $a_{i+1} - a_i$ tend to infinity.

Equivalently: for every bound $B$, only finitely many $P$-smooth numbers $n$ have
another $P$-smooth number within distance $B$ above them.

Proved by Tijdeman [Ti73].
-/
@[category research solved, AMS 11]
theorem erdos_240 :
    answer(True) ↔
      ∃ P : Set ℕ, Set.Infinite P ∧ (∀ p ∈ P, Nat.Prime p) ∧
        ∀ B : ℕ, Set.Finite {n : ℕ | n ∈ smoothNumbers P ∧
          ∃ m ∈ smoothNumbers P, n < m ∧ m ≤ n + B} := by
  sorry

/--
Tijdeman's quantitative strengthening of Erdős Problem 240 [Ti73]:
For any $\varepsilon > 0$, there exists an infinite set of primes $P$ such that the
consecutive gaps of $P$-smooth numbers satisfy $a_{i+1} - a_i \gg a_i^{1-\varepsilon}$.

That is, there exists a constant $c > 0$ such that for all sufficiently large
$P$-smooth numbers $n$, the next $P$-smooth number after $n$ is at least
$n + c \cdot n^{1-\varepsilon}$.
-/
@[category research solved, AMS 11]
theorem erdos_240_tijdeman_quantitative :
    ∀ ε : ℝ, ε > 0 →
      ∃ P : Set ℕ, Set.Infinite P ∧ (∀ p ∈ P, Nat.Prime p) ∧
        ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in Filter.atTop,
          n ∈ smoothNumbers P →
            ∀ m ∈ smoothNumbers P, n < m → c * (n : ℝ) ^ (1 - ε) ≤ (m - n : ℝ) := by
  sorry

end Erdos240
