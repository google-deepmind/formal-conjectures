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
  _Internat. J. Algebra Comput._ 4 (1994), 1-308.
- [Ly96] I. G. Lysënok. "Infinite Burnside groups of even exponent."
  _Izv. Ross. Akad. Nauk Ser. Mat._ 60 (1996), 3-224.
- [Bu02] W. Burnside. "On an unsettled question in the theory of discontinuous groups."
  _Quart. J. Pure Appl. Math._ 33 (1902), 230-238.
- [Sa40] I. N. Sanov. "Solution of Burnside's problem for exponent 4."
  _Leningrad State Univ. Annals (Uchenye Zapiski) Math. Ser._ 10 (1940), 166-170.
- [Ha58] M. Hall. "Solution of the Burnside problem for exponent six."
  _Illinois J. Math._ 2 (1958), 764-786.
-/

namespace BoundedBurnsideProblem

/--
Let $G$ be a finitely generated group, and assume there exists $n$ such that for every $g$ in $G$,
$g^n = 1$. Must $G$ be finite?

The answer is negative. Novikov and Adian proved that for every odd $n > 4381$ there exist
infinite, finitely generated groups of exponent $n$ [NA68]; Adian later reduced this to odd
$n > 665$ [Ad79]. The even case is harder: Ivanov proved $B(m, n)$ infinite for $m > 1$ and
even $n \ge 2^{48}$ divisible by $2^9$ [Iv94], and Lysënok improved this to $m > 1$ and
$n \ge 8000$ [Ly96]. Any such group, for example the free Burnside group $B(2, 667)$,
refutes the statement below.

Note this concerns only the universally quantified question stated here, which a single
counterexample closes. The classification of which free Burnside groups $B(m, n)$ are finite
remains open, with $B(2, 5)$ the best known open case.
-/
@[category research solved, AMS 20]
theorem bounded_burnside_problem :
    answer(False) ↔ ∀ (G : Type) [Group G] (fin_gen : Group.FG G)
      (n : ℕ) (hn : n > 0) (bounded : ∀ g : G, g^n = 1), Finite G := by
  sorry

/--
The **free Burnside group** $B(m, n)$ of rank $m$ and exponent $n$: the group with $m$
generators in which $x^n = 1$ holds for every element, i.e. the quotient of the free group on
$m$ generators by the normal closure of all $n$-th powers. Every group with $m$ generators in
which $g^n = 1$ for all $g$ is a quotient of $B(m, n)$, so the bounded Burnside problem is the
question of which $B(m, n)$ are finite.
-/
abbrev freeBurnsideGroup (m n : ℕ) : Type :=
  PresentedGroup (Set.range fun w : FreeGroup (Fin m) => w ^ n)

/-- Every element of $B(m, n)$ satisfies $g^n = 1$. -/
@[category API, AMS 20]
theorem freeBurnsideGroup_pow_eq_one (m n : ℕ) (g : freeBurnsideGroup m n) : g ^ n = 1 := by
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ g
  rw [← map_pow, PresentedGroup.mk_eq_one_iff]
  exact Subgroup.subset_normalClosure ⟨w, rfl⟩

/--
**Burnside problem II** ([Wikipedia]): for which $m$ and $n$ is the free Burnside group
$B(m, n)$ finite?

Known: $B(m, n)$ is finite for $n \in \{1, 2, 3, 4, 6\}$ and for $m = 1$, and infinite for
$m \ge 2$ and odd $n \ge 665$ or $n \ge 8000$; see the variants below. The smallest open case
is $B(2, 5)$.
-/
@[category research open, AMS 20]
theorem burnside_problem_II :
    {p : ℕ × ℕ | Finite (freeBurnsideGroup p.1 p.2)} = answer(sorry) := by
  sorry

/-- Is $B(2, 5)$ finite? This is the smallest open case of Burnside problem II. -/
@[category research open, AMS 20]
theorem finite_freeBurnsideGroup_two_five :
    answer(sorry) ↔ Finite (freeBurnsideGroup 2 5) := by
  sorry

/-- $B(1, n)$ is the cyclic group of order $n$, so it is finite for $n \ge 1$ [Bu02]. -/
@[category research solved, AMS 20]
theorem finite_freeBurnsideGroup_one (n : ℕ) (hn : 0 < n) : Finite (freeBurnsideGroup 1 n) := by
  sorry

/-- $B(m, 2)$ is the direct product of $m$ copies of the cyclic group of order $2$, hence
finite [Bu02]. -/
@[category research solved, AMS 20]
theorem finite_freeBurnsideGroup_two (m : ℕ) : Finite (freeBurnsideGroup m 2) := by
  sorry

/-- $B(m, 3)$ is finite for all $m$ [Bu02]. -/
@[category research solved, AMS 20]
theorem finite_freeBurnsideGroup_three (m : ℕ) : Finite (freeBurnsideGroup m 3) := by
  sorry

/-- $B(m, 4)$ is finite for all $m$ (Sanov [Sa40]). -/
@[category research solved, AMS 20]
theorem finite_freeBurnsideGroup_four (m : ℕ) : Finite (freeBurnsideGroup m 4) := by
  sorry

/-- $B(m, 6)$ is finite for all $m$ (M. Hall [Ha58]). -/
@[category research solved, AMS 20]
theorem finite_freeBurnsideGroup_six (m : ℕ) : Finite (freeBurnsideGroup m 6) := by
  sorry

/-- Novikov–Adian [NA68], Adian [Ad79]: $B(m, n)$ is infinite for $m \ge 2$ and odd
$n \ge 665$. -/
@[category research solved, AMS 20]
theorem infinite_freeBurnsideGroup_of_odd (m n : ℕ) (hm : 2 ≤ m) (hn : Odd n) (h : 665 ≤ n) :
    Infinite (freeBurnsideGroup m n) := by
  sorry

/-- Lysënok [Ly96] (with [Ad79] for odd exponents): $B(m, n)$ is infinite for $m \ge 2$ and
$n \ge 8000$. -/
@[category research solved, AMS 20]
theorem infinite_freeBurnsideGroup_of_le (m n : ℕ) (hm : 2 ≤ m) (h : 8000 ≤ n) :
    Infinite (freeBurnsideGroup m n) := by
  sorry

/-- $B(m, 1)$ is the trivial group. -/
@[category test, AMS 20]
theorem subsingleton_freeBurnsideGroup_one (m : ℕ) : Subsingleton (freeBurnsideGroup m 1) := by
  have h : ∀ w : FreeGroup (Fin m),
      PresentedGroup.mk (Set.range fun w : FreeGroup (Fin m) => w ^ 1) w = 1 := fun w =>
    PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ⟨w, pow_one w⟩)
  refine ⟨fun a b => ?_⟩
  obtain ⟨wa, rfl⟩ := PresentedGroup.mk_surjective _ a
  obtain ⟨wb, rfl⟩ := PresentedGroup.mk_surjective _ b
  rw [h wa, h wb]

end BoundedBurnsideProblem
