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
# Erdős Problem 18

*Reference:* [erdosproblems.com/18](https://www.erdosproblems.com/18)

We call $m$ *practical* if every integer $1 \leq n < m$ is the sum of distinct divisors
of $m$. If $m$ is practical, let $h(m)$ be the least $k$ such that every $1 \leq n < m$
is the sum of at most $k$ distinct divisors of $m$.

Three questions:
1. Are there infinitely many practical $m$ such that $h(m) < (\log \log m)^{O(1)}$?
2. Is it true that $h(n!) < n^{o(1)}$?
3. Or perhaps even $h(n!) < (\log n)^{O(1)}$?

Known: Erdős showed $h(n!) < n$. Vose [Vo85] proved infinitely many practical $m$ with
$h(m) \ll (\log m)^{1/2}$. Erdős offered \$250 for a proof or disproof of whether
$h(n!) < (\log n)^{O(1)}$ [Er81h, p.172].

Related problems: [erdosproblems.com/304](https://www.erdosproblems.com/304),
[erdosproblems.com/825](https://www.erdosproblems.com/825).

OEIS: [A005153](https://oeis.org/A005153) — practical numbers.

## References

- [Er74b] Erdős, P. (1974).
- [Er79] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. **52** (1979), 67–70.
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number theory_. Monographies de L'Enseignement Mathematique (1980).
- [Er81h] Erdős, P., _Some problems and results on additive and multiplicative number theory_. Analytic number theory (Philadelphia, Pa., 1980) (1981), 171–182.
- [Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_. Combinatorics '94 (Catania), Congressus Numerantium **107** (1995).
- [Er96b] Erdős, P., _Some problems I presented or planned to present in my short talk_. Analytic number theory, Vol. 1 (Allerton Park, IL, 1995) (1996), 333–335.
- [Er98] Erdős, P., _Some of my new and almost new problems and results in combinatorial number theory_. Number theory (Eger, 1996) (1998), 169–180.
- [Vo85] Vose, Michael D., _Egyptian fractions_. Bull. London Math. Soc. (1985), 21–24.
-/

open Real Filter

namespace Erdos18

/-- $m$ is practical if every integer $1 \leq n < m$ can be represented as a sum
    of distinct divisors of $m$. -/
def IsPractical (m : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n < m →
    ∃ S : Finset ℕ, S ⊆ Nat.divisors m ∧ S.sum id = n

/-- For a practical number $m$, $\mathrm{practicalH}(m)$ is the minimum $k$ such that every
    integer $1 \leq n < m$ can be expressed as the sum of at most $k$ distinct
    divisors of $m$. -/
noncomputable def practicalH (m : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ n : ℕ, 1 ≤ n → n < m →
    ∃ S : Finset ℕ, S ⊆ Nat.divisors m ∧ S.card ≤ k ∧ S.sum id = n}

/--
Erdős Problem 18 [Er74b, Er79, ErGr80, Er81h (p.172), Er95, Er96b, Er98]:

Conjecture (1): There are infinitely many practical $m$ such that
$h(m) < (\log \log m)^{O(1)}$, i.e., there exists a constant $C > 0$ such that
infinitely many practical $m$ satisfy $h(m) < (\log \log m)^C$.
-/
@[category research open, AMS 11]
theorem erdos_18 :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∃ m : ℕ, m ≥ N ∧ IsPractical m ∧
      (practicalH m : ℝ) < (Real.log (Real.log (m : ℝ))) ^ C := by
  sorry

/--
Erdős Problem 18 [Er74b, Er79, ErGr80, Er81h (p.172), Er95, Er96b, Er98]:

Conjecture (2): $h(n!) < n^{o(1)}$, i.e., for every $\varepsilon > 0$, for all
sufficiently large $n$, $h(n!) < n^\varepsilon$.
-/
@[category research open, AMS 11]
theorem erdos_18.variants.factorial_subpolynomial :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (practicalH n.factorial : ℝ) < (n : ℝ) ^ ε := by
  sorry

/--
Erdős Problem 18 [Er74b, Er79, ErGr80, Er81h (p.172), Er95, Er96b, Er98]:

Conjecture (3): $h(n!) < (\log n)^{O(1)}$, i.e., there exists a constant $C > 0$
such that for all sufficiently large $n$, $h(n!) < (\log n)^C$.

Erdős offered \$250 for a proof or disproof of this statement [Er81h, p.172].
-/
@[category research open, AMS 11]
theorem erdos_18.variants.factorial_polylog :
    answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (practicalH n.factorial : ℝ) < (Real.log (n : ℝ)) ^ C := by
  sorry

end Erdos18
