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
# Rudin's conjecture on squares in arithmetic progressions

For $q, a \ge 1$, let $Q(N; q, a)$ denote the number of perfect squares among the first $N$ terms
$\{qn + a : 0 \le n < N\}$ of the arithmetic progression with common difference $q$ and initial
term $a$. Let
$$Q(N) = \max Q(N; q, a),$$
where the maximum is taken over all *non-trivial* progressions, i.e. those with $\gcd(q, a) = 1$
and $(q, a) \neq (1, 1)$. (The excluded progression $n \mapsto n + 1$ trivially consists of every
positive integer, so it contains $\sim \sqrt{N}$ squares but is not of interest.)

**Rudin's conjecture** [Ru60] asserts that
$$Q(N) = O(\sqrt{N}).$$
A stronger form states that for $N \ge 6$ the progression $24n + 1$ attains the maximum, and is
the unique progression (up to equivalence) doing so.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Rudin%27s_conjecture)
- [Ru60] Rudin, W., *Trigonometric series with gaps*, J. Math. Mech. 9 (1960), 203–227.
- González-Jiménez, E. and Xarles, X., *On a conjecture of Rudin on squares in arithmetic
  progressions*, LMS J. Comput. Math. 17 (2014), 58–76.
-/

open Filter Asymptotics Real

namespace RudinsConjecture

/-- $Q(N; q, a)$ is the number of perfect squares among the first $N$ terms of the arithmetic
progression $\{q n + a : 0 \le n < N\}$. -/
noncomputable abbrev Q (N q a : ℕ) : ℕ := {n : ℕ | n < N ∧ IsSquare (q * n + a)}.ncard

/-- A pair $(q, a)$ describes a *non-trivial* arithmetic progression if $q, a \ge 1$,
$\gcd(q, a) = 1$, and $(q, a) \neq (1, 1)$. -/
def IsNontrivial (q a : ℕ) : Prop :=
  1 ≤ q ∧ 1 ≤ a ∧ Nat.Coprime q a ∧ (q, a) ≠ (1, 1)

/-- $Q(N) = \max Q(N; q, a)$, the largest number of perfect squares occurring among the first
$N$ terms of any non-trivial arithmetic progression. The supremum is over a set of naturals that
is bounded above by $N$ (each progression has only $N$ terms), so it is attained. -/
noncomputable def Qmax (N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ q a : ℕ, IsNontrivial q a ∧ Q N q a = m}

/-- Sanity check: the progression $24 n + 1$ is non-trivial. -/
@[category test, AMS 11]
theorem isNontrivial_24_1 : IsNontrivial 24 1 := by
  refine ⟨by norm_num, by norm_num, by decide, by decide⟩

/-- Sanity check: there are no squares among the first `0` terms of any progression. -/
@[category test, AMS 11]
theorem Q_zero (q a : ℕ) : Q 0 q a = 0 := by
  simp [Q]

/-- Sanity check pinning `Q` to a concrete value: among the first `6` terms of `24 n + 1`, namely
`1, 25, 49, 73, 97, 121`, exactly four are perfect squares (`1, 25, 49, 121`), so
`Q 6 24 1 = 4`. This validates the definition of `Q` and matches the claim that `24 n + 1` is the
extremal progression. -/
@[category test, AMS 11]
theorem Q_six_twentyfour_one : Q 6 24 1 = 4 := by
  show ({n : ℕ | n < 6 ∧ IsSquare (24 * n + 1)}).ncard = 4
  have hset : {n : ℕ | n < 6 ∧ IsSquare (24 * n + 1)} = ({0, 1, 2, 5} : Set ℕ) := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hn, hsq⟩
      interval_cases n
      · omega
      · omega
      · omega
      · exfalso; obtain ⟨r, hr⟩ := hsq
        have hb : r < 9 := by nlinarith
        interval_cases r <;> omega
      · exfalso; obtain ⟨r, hr⟩ := hsq
        have hb : r < 10 := by nlinarith
        interval_cases r <;> omega
      · omega
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨by norm_num, 1, by norm_num⟩
      · exact ⟨by norm_num, 5, by norm_num⟩
      · exact ⟨by norm_num, 7, by norm_num⟩
      · exact ⟨by norm_num, 11, by norm_num⟩
  rw [hset]
  have hcoe : ({0, 1, 2, 5} : Set ℕ) = ↑({0, 1, 2, 5} : Finset ℕ) := by simp
  rw [hcoe, Set.ncard_coe_finset]
  decide

/--
**Rudin's conjecture.** The maximal number of squares among the first $N$ terms of a non-trivial
arithmetic progression grows at most like $\sqrt{N}$:
$$Q(N) = O(\sqrt{N}).$$
-/
@[category research open, AMS 11]
theorem rudins_conjecture :
    (fun N : ℕ => (Qmax N : ℝ)) =O[atTop] fun N : ℕ => Real.sqrt N := by
  sorry

/--
A stronger form of Rudin's conjecture: for every $N \ge 6$, the arithmetic progression
$24 n + 1$ attains the maximum $Q(N)$.
-/
@[category research open, AMS 11]
theorem rudins_conjecture_strong (N : ℕ) (hN : 6 ≤ N) : Q N 24 1 = Qmax N := by
  sorry

/--
The strongest form of Rudin's conjecture also asserts *uniqueness*: for $N \ge 6$, any non-trivial
arithmetic progression attaining the maximum $Q(N)$ has common difference $24$. (Its initial term
is then forced by $\gcd(24, a) = 1$; the progression $24n + 1$ is the canonical representative.)
-/
@[category research open, AMS 11]
theorem rudins_conjecture_unique (N : ℕ) (hN : 6 ≤ N) (q a : ℕ)
    (hqa : IsNontrivial q a) (hmax : Q N q a = Qmax N) : q = 24 := by
  sorry

end RudinsConjecture
