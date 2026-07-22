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
# Erdős Problem 649

*References:*
- [erdosproblems.com/649](https://www.erdosproblems.com/649)
- [Er95c] Erdős, Paul, *Some problems in number theory*. Octogon Math. Mag. (1995), 3-5.
- [Ma35] Mahler, Kurt, *Über den grössten Primteiler spezieller Polynome zweiten Grades*. Archiv
  für math. og naturvid (1935).
- [Ro64b] Rotkiewicz, André, *Sur les nombres naturels $n$ et $k$ tels que les nombres $n$ et $nk$
  sont à la fois pseudopremiers*. Atti Accad. Naz. Lincei Rend. Cl. Sci. Fis. Mat. Nat. (8)
  (1964), 816-818.
-/

namespace Erdos649

/--
Let $P(m)$ denote the greatest prime factor of $m$. Is it true that, for any two primes $p,q$,
there exists some integer $n$ such that $P(n)=p$ and $P(n+1)=q$?

In fact, the answer to this question as written is easily seen to be no, since there are no
solutions to $2^k\equiv -1\pmod{7}$, and hence this fails with $p=2$ and $q=7$. It is possible
that Erdős meant to exclude such obstructions, by amending this to 'odd primes' or 'all
sufficiently large primes' or such.
-/
@[category research solved, AMS 11]
theorem erdos_649 : answer(False) ↔
    ∀ p q : ℕ, p.Prime → q.Prime →
      ∃ n : ℕ, n.maxPrimeFac = p ∧ (n + 1).maxPrimeFac = q := by
  sorry

/--
In fact, the answer to this question as written is easily seen to be no, since there are no
solutions to $2^k\equiv -1\pmod{7}$, and hence this fails with $p=2$ and $q=7$.
-/
@[category textbook, AMS 11]
theorem erdos_649.variants.no_solution_two_seven :
    ¬ ∃ n : ℕ, n.maxPrimeFac = 2 ∧ (n + 1).maxPrimeFac = 7 := by
  sorry

/--
Even with such amendments, this problem is false in a strong sense: Alan Tong has provided the
following elegant elementary proof that, for any given prime $p$, there are infinitely many
primes $q$ such that this statement is false: let $m$ be the product of all primes $\leq p$, and
choose a prime $q$ congruent to $-1$ modulo $4m$. If $p$ is the greatest prime divisor of $n$
then, using quadratic reciprocity, every prime divisor of $n$ is a quadratic residue modulo $q$,
and hence $n$ is a quadratic residue modulo $q$. On the other hand, since $q\equiv 3\pmod{4}$ we
know that $-1$ is not a quadratic residue modulo $q$, and hence $n\not\equiv -1\pmod{q}$, so it
is impossible for $q\mid n+1$.
-/
@[category research solved, AMS 11]
theorem erdos_649.variants.tong (p : ℕ) (hp : p.Prime) :
    {q : ℕ |
      q.Prime ∧ ¬ ∃ n : ℕ, n.maxPrimeFac = p ∧ (n + 1).maxPrimeFac = q}.Infinite := by
  sorry

/--
Tong asks whether, for any given odd prime $q$, there are infinitely many primes $p$ such that
there is no integer $n$ with $P(n)=p$ and $P(n+1)=q$.
-/
@[category research open, AMS 11]
theorem erdos_649.variants.tong_question : answer(sorry) ↔
    ∀ q : ℕ, q.Prime → Odd q →
      {p : ℕ |
        p.Prime ∧ ¬ ∃ n : ℕ, n.maxPrimeFac = p ∧ (n + 1).maxPrimeFac = q}.Infinite := by
  sorry

/--
Sampaio independently observed that the answer to Erdős' original problem is no if one of the
primes can be $2$ - for example this is false with $p=19$ and $q=2$, since if $n+1=2^k$ and
$19\mid n$ then (since $2$ is a primitive root modulo $19$) we must have $18\mid k$, and hence
$73\mid 2^{18}-1\mid n$.
-/
@[category textbook, AMS 11]
theorem erdos_649.variants.sampaio :
    ¬ ∃ n : ℕ, n.maxPrimeFac = 19 ∧ (n + 1).maxPrimeFac = 2 := by
  sorry

/--
Problem 6 in the 12th Romanian Master of Mathematics Competitions in 2020 was to prove that there
exist infinitely many odd primes $p$ such that, for every $n$, $P(n)P(n+1)\neq 2p$.
-/
@[category textbook, AMS 11]
theorem erdos_649.variants.rmm_2020 :
    {p : ℕ | p.Prime ∧ Odd p ∧
      ∀ n : ℕ, n.maxPrimeFac * (n + 1).maxPrimeFac ≠ 2 * p}.Infinite := by
  sorry

end Erdos649
