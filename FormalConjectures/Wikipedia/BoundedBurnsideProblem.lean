/-
Copyright 2025 The Formal Conjectures Authors.

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
# Bounded Burnside problem

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Burnside_problem#Bounded_Burnside_problem)
- [NA68] P. S. Novikov, S. I. Adian. "Infinite periodic groups I-III."
  _Izv. Akad. Nauk SSSR Ser. Mat._ 32 (1968).
- [Ad79] S. I. Adian. _The Burnside Problem and Identities in Groups._ Springer, 1979.
- [Iv94] S. V. Ivanov. "The free Burnside groups of sufficiently large exponents."
  _Internat. J. Algebra Comput._ 4 (1994).
-/

namespace BoundedBurnsideProblem

/--
Let $G$ be a finitely generated group, and assume there exists $n$ such that for every $g$ in $G$,
$g^n = 1$. Must $G$ be finite?

The answer is negative. Novikov and Adian proved that for every odd $n > 4381$ there exist
infinite, finitely generated groups of exponent $n$ [NA68]; Adian later reduced this to odd
$n > 665$ [Ad79], and Ivanov settled sufficiently large even exponents [Iv94]. Any such group,
for example the free Burnside group $B(2, 667)$, refutes the statement below.

Note this concerns only the universally quantified question stated here, which a single
counterexample closes. The classification of which free Burnside groups $B(m, n)$ are finite
remains open, with $B(2, 5)$ the best known open case.
-/
@[category research solved, AMS 20]
theorem bounded_burnside_problem :
    answer(False) ↔ ∀ (G : Type) [Group G] (fin_gen : Group.FG G)
      (n : ℕ) (hn : n > 0) (bounded : ∀ g : G, g^n = 1), Finite G := by
  sorry

end BoundedBurnsideProblem
