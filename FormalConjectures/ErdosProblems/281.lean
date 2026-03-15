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
import FormalConjecturesForMathlib.Data.Set.Density

/-!
# Erdős Problem 281

*Reference:* [erdosproblems.com/281](https://www.erdosproblems.com/281)

Let $n_1 < n_2 < \cdots$ be a strictly increasing sequence of positive integers such that,
for any choice of congruence classes $a_i \pmod{n_i}$, the integers not satisfying any of the
congruences have density $0$. Is it true that for every $\varepsilon > 0$ there exists some $k$
such that the density of integers avoiding the first $k$ congruences is already less than
$\varepsilon$, regardless of the choice of $a_i$?

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).

[DaEr36] Davenport, H. and Erdős, P., _On sequences of positive integers_.
Acta Arithmetica **2** (1936), 147-151.

[HaRo66] Halberstam, H. and Roth, K. F., _Sequences. Vol. I_.
Oxford University Press (1966).
-/

open Classical Set

namespace Erdos281

/--
Erdős Problem 281 (Proved) [ErGr80, p.29]:

Let $n_1 < n_2 < \cdots$ be a strictly increasing sequence of positive integers such that,
for any choice of congruence classes $a_i \pmod{n_i}$, the set of integers not satisfying
any of the congruences has density $0$. Then for every $\varepsilon > 0$ there exists some $k$
such that, for every choice of congruence classes $a_i$, the density of integers not
satisfying any of the congruences $a_i \pmod{n_i}$ for $i < k$ is less than $\varepsilon$.

The proof combines the Davenport–Erdős theorem [DaEr36] with Rogers' optimal sieve
bound [HaRo66].
-/
@[category research solved, AMS 11]
theorem erdos_281 : answer(True) ↔
    ∀ (n : ℕ → ℕ), (∀ i, 0 < n i) → StrictMono n →
    (∀ a : ℕ → ℕ, {m : ℕ | ∀ i, ¬(m ≡ a i [MOD n i])}.HasDensity 0) →
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ,
      {m : ℕ | ∀ i, i < k → ¬(m ≡ a i [MOD n i])}.upperDensity < ε := by
  sorry

end Erdos281
