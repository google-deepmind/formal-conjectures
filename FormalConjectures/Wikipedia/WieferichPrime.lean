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
# Wieferich primes

A Wieferich prime is a prime $p$ with $2^{p-1} \equiv 1 \pmod{p^2}$. The only known examples are
$1093$ and $3511$. It is conjectured that there are infinitely many Wieferich primes; a heuristic
argument suggests that the number of Wieferich primes up to $x$ grows like $\log \log x$.

More generally, a prime $p$ is a Wieferich prime to base $a$ if $a^{p-1} \equiv 1 \pmod{p^2}$.
Wikipedia's list of unsolved problems also asks whether there are infinitely many Wieferich primes
to every base $a > 0$, and whether there is any Wieferich prime to base $47$. It is also not known
whether there is any Wieferich prime besides $1093$ and $3511$.

*References:*
* [Wikipedia, List of unsolved problems in mathematics](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics)
* [Wikipedia, Wieferich prime](https://en.wikipedia.org/wiki/Wieferich_prime)
* [OEIS A001220](https://oeis.org/A001220)
* P. Ribenboim, *Die Welt der Primzahlen*, 2nd ed., Springer (2006), pp. 242–243.
* [PrimeGrid, Wieferich and Wall–Sun–Sun Prime Search](https://www.primegrid.com/stats_ww.php)
-/

namespace WieferichPrime

/-- There are infinitely many Wieferich primes. -/
@[category research open, AMS 11]
theorem infinite_isWieferichPrime : {p : ℕ | IsWieferichPrime p}.Infinite := by
  sorry

/--
Are $1093$ and $3511$ the only Wieferich primes? They are the only known ones: PrimeGrid's search,
completed in 2022, shows that any other Wieferich prime exceeds $2^{64}$. On the other hand, the
heuristic count of $\log \log x$ Wieferich primes up to $x$ predicts that there are infinitely
many, see `infinite_isWieferichPrime`.
-/
@[category research open, AMS 11]
theorem isWieferichPrime_iff :
    answer(sorry) ↔ ∀ p, IsWieferichPrime p ↔ p = 1093 ∨ p = 3511 := by
  sorry

/--
For any given integer $a > 0$, are there infinitely many primes $p$ such that
$a^{p-1} \equiv 1 \pmod{p^2}$? The case $a = 1$ is trivial, since every prime qualifies
(`isWieferichPrimeBase_one_iff`). So is the case $a = 0$ under our definition
(`isWieferichPrimeBase_zero_iff`), which is why the source's restriction to $a > 0$ is dropped.
-/
@[category research open, AMS 11]
theorem infinite_isWieferichPrimeBase :
    answer(sorry) ↔ ∀ a : ℕ, {p : ℕ | IsWieferichPrimeBase a p}.Infinite := by
  sorry

/-- Are there any Wieferich primes to base $47$? None is currently known. -/
@[category research open, AMS 11]
theorem exists_isWieferichPrimeBase_47 : answer(sorry) ↔ ∃ p, IsWieferichPrimeBase 47 p := by
  sorry

/-- The prime $1093$ is a Wieferich prime: $2^{1092} \equiv 1 \pmod{1093^2}$. -/
@[category test, AMS 11]
theorem isWieferichPrime_1093 : IsWieferichPrime 1093 := by
  decide +kernel

/-- The prime $3511$ is a Wieferich prime: $2^{3510} \equiv 1 \pmod{3511^2}$. -/
@[category test, AMS 11]
theorem isWieferichPrime_3511 : IsWieferichPrime 3511 :=
  ⟨by norm_num, by decide +kernel⟩

/-- The prime $2$ is not a Wieferich prime, so no hypothesis excluding it is needed. -/
@[category test, AMS 11]
theorem not_isWieferichPrime_two : ¬ IsWieferichPrime 2 := by
  decide

end WieferichPrime
