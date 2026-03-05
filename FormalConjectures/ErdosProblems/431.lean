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
# Erdős Problem 431

*Reference:* [erdosproblems.com/431](https://www.erdosproblems.com/431)

Are there two infinite sets $A$ and $B$ of natural numbers such that the sumset
$A + B = \{a + b \mid a \in A, b \in B\}$ agrees with the set of prime numbers up to
finitely many exceptions?

This is a problem of Ostmann, sometimes known as the 'inverse Goldbach problem'.
The expected answer is no.

Elsholtz and Harper [ElHa15] showed that if $A$, $B$ are such sets then for all
large $x$ we must have
$x^{1/2}/(\log x \cdot \log \log x) \ll |A \cap [1,x]| \ll x^{1/2} \cdot \log \log x$
and similarly for $B$.

Elsholtz [El01] proved there are no sets $A$, $B$, $C$ (all of size at least 2) such that
$A + B + C$ agrees with the primes up to finitely many exceptions.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).

[ElHa15] Elsholtz, C. and Harper, A. J., _Additive decompositions of sets with restricted
prime factors_, (2015).

[El01] Elsholtz, C., _A remark on Hofmann's conjecture_, (2001).
-/

namespace Erdos431

/--
Erdős Problem 431 [ErGr80]: Are there two infinite sets $A$ and $B$ of natural
numbers such that the sumset $A + B = \{a + b \mid a \in A, b \in B\}$ agrees with
the set of prime numbers up to finitely many exceptions?
-/
@[category research open, AMS 11]
theorem erdos_431 : answer(sorry) ↔
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧
      (symmDiff (Set.image2 (· + ·) A B) {n | n.Prime}).Finite := by
  sorry

end Erdos431
