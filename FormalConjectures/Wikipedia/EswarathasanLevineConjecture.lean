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
module

public import FormalConjecturesUtil

/-!
# Eswarathasan–Levine conjectures on harmonic numerators

Given a prime $p$, write $J_p$ for the set of indices $n \ge 1$ where $p$ divides the reduced
numerator of $H_n = \sum_{k=1}^n \frac{1}{k}$ (for instance $J_2 = \emptyset$ and
$J_3 = \{2, 7, 22\}$). Arulappah Eswarathasan and Eugene Levine (1991) showed that
$\{p - 1, p^2 - p, p^2 - 1\} \subseteq J_p$ whenever $p \ge 5$, called a prime $p \ge 5$ a
*harmonic prime* ([OEIS A092101](https://oeis.org/A092101)) when $J_p$ consists solely of those
three elements ($|J_p| = 3$), and conjectured both that every $J_p$ is finite and that infinitely
many harmonic primes exist. David W. Boyd (1994) confirmed finiteness of $J_p$ for all primes
$p \le 547$ aside from $83, 127, 397$ and proposed a $1 / e$ relative density heuristic for harmonic
primes.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Harmonic_number#Arithmetic_properties)
- [OEIS A092101](https://oeis.org/A092101)
- A. Eswarathasan and E. Levine (1991), Discrete Math. **91**, no. 3, 249–257.
- D. W. Boyd (1994), Experiment. Math. **3**, no. 4, 287–302.
-/

@[expose] public section

namespace EswarathasanLevineConjecture

/-- Indices $n \ge 1$ whose $n$-th harmonic sum $H_n$ has reduced numerator divisible by $p$.
The bound $1 \le n$ rules out $n = 0$, where `harmonic 0 = 0` has numerator $0$. -/
def harmonicNumDivisibleSet (p : ℕ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ (p : ℤ) ∣ (harmonic n).num}

/-- A prime $p \ge 5$ is a *harmonic prime* ([OEIS A092101](https://oeis.org/A092101)) if $J_p$ has
cardinality $3$, i.e. $J_p = \{p - 1, p^2 - p, p^2 - 1\}$. Note that $p = 3$ also satisfies
$|J_3| = 3$ via $J_3 = \{2, 7, 22\}$, so Boyd (1994) and [OEIS A092101](https://oeis.org/A092101)
require $5 \le p$; this single-prime convention does not affect
`eswarathasan_levine_harmonic_primes_infinite`. -/
def IsHarmonicPrime (p : ℕ) : Prop :=
  p.Prime ∧ 5 ≤ p ∧ (harmonicNumDivisibleSet p).ncard = 3

/-- Boundary and small-index check at $p = 3$: $0, 1, 3 \notin J_3$ whereas $2 \in J_3$
($H_2 = 3/2$). -/
@[category test, AMS 11]
theorem harmonicNumDivisibleSet_three_small :
    0 ∉ harmonicNumDivisibleSet 3 ∧
      1 ∉ harmonicNumDivisibleSet 3 ∧
      2 ∈ harmonicNumDivisibleSet 3 ∧
      3 ∉ harmonicNumDivisibleSet 3 := by
  simp only [harmonicNumDivisibleSet, Set.mem_ofPred_eq]
  norm_num [harmonic]

/-- For $p = 2$, none of $0, 1, 2, 3, 4$ belong to $J_2$. -/
@[category test, AMS 11]
theorem harmonicNumDivisibleSet_two_small :
    ∀ n ∈ ({0, 1, 2, 3, 4} : Finset ℕ), n ∉ harmonicNumDivisibleSet 2 := by
  intro n hn
  fin_cases hn <;> simp [harmonicNumDivisibleSet, harmonic] <;> norm_num

/-- Every $H_n$ with $n \ge 1$ has odd reduced numerator, hence $J_2 = \emptyset$. -/
@[category textbook, AMS 11]
theorem harmonicNumDivisibleSet_two_empty : harmonicNumDivisibleSet 2 = ∅ := by
  sorry

/-- Eswarathasan–Levine inclusion theorem (1991): every prime $p \ge 5$ satisfies
$\{p - 1, p^2 - p, p^2 - 1\} \subseteq J_p$ (using Wolstenholme's theorem at $p - 1$; cf.
`WolstenholmePrime.wolstenholme_theorem` and `WolstenholmePrime.wolstenholme_harmonic`). -/
@[category research solved, AMS 11]
theorem eswarathasan_levine_three_elements_subset {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ({p - 1, p ^ 2 - p, p ^ 2 - 1} : Set ℕ) ⊆ harmonicNumDivisibleSet p := by
  sorry

/-- Eswarathasan–Levine finiteness conjecture (1991): $J_p$ is finite for every prime $p$. -/
@[category research open, AMS 11]
theorem eswarathasan_levine_harmonic_conjecture {p : ℕ} (hp : p.Prime) :
    (harmonicNumDivisibleSet p).Finite := by
  sorry

/-- Eswarathasan–Levine harmonic-prime conjecture (1991): infinitely many primes $p$ satisfy
$|J_p| = 3$. -/
@[category research open, AMS 11]
theorem eswarathasan_levine_harmonic_primes_infinite :
    {p : ℕ | IsHarmonicPrime p}.Infinite := by
  sorry

end EswarathasanLevineConjecture
