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
# Erdős Problem 902

*Reference:* [erdosproblems.com/902](https://www.erdosproblems.com/902)

Let $f(n)$ be minimal such that there is a tournament (a complete directed graph)
on $f(n)$ vertices such that every set of $n$ vertices is dominated by at least one
other vertex. Estimate $f(n)$.

Schütte asked Erdős this in the early 1960s. It is easy to check that
$f(1) = 3$ and $f(2) = 7$.

[Er63c] Erdős, P. (1963).

[SzSz65] Szekeres, E. and Szekeres, G. (1965).
-/

namespace Erdos902

/-- A tournament on a type $V$: a relation where for any two distinct vertices,
exactly one beats the other. -/
structure Tournament (V : Type*) where
  beats : V → V → Prop
  irrefl : ∀ v, ¬beats v v
  complete : ∀ v w, v ≠ w → (beats v w ∨ beats w v)
  antisymm : ∀ v w, beats v w → ¬beats w v

/-- A tournament has the $n$-domination property if every subset of size $n$
is dominated by some vertex outside the subset (i.e., some vertex $v \notin S$
beats every member of $S$). -/
def Tournament.hasDominationProperty {V : Type*} (T : Tournament V)
    (n : ℕ) : Prop :=
  ∀ S : Finset V, S.card = n → ∃ v, v ∉ S ∧ ∀ u ∈ S, T.beats v u

/-- $f(n)$: the minimum number of vertices in a tournament with the
$n$-domination property. -/
noncomputable def tournamentDominationNumber (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (T : Tournament (Fin m)), T.hasDominationProperty n}

/--
Erdős Problem 902, lower bound [Er63c]: $f(n) \geq 2^{n+1} - 1$ for all $n \geq 1$.
-/
@[category research solved, AMS 5]
theorem erdos_902 (n : ℕ) (hn : n ≥ 1) :
    tournamentDominationNumber n ≥ 2 ^ (n + 1) - 1 := by
  sorry

/--
Erdős Problem 902, upper bound [Er63c]: $f(n) \ll n^2 \cdot 2^n$.
There exists $C > 0$ such that $f(n) \leq C \cdot n^2 \cdot 2^n$ for all $n \geq 1$.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (tournamentDominationNumber n : ℝ) ≤ C * (n : ℝ) ^ 2 * 2 ^ n := by
  sorry

/--
Szekeres–Szekeres improved lower bound [SzSz65]: $f(n) \gg n \cdot 2^n$.
There exists $C > 0$ such that $f(n) \geq C \cdot n \cdot 2^n$ for all $n \geq 1$.
-/
@[category research solved, AMS 5]
theorem erdos_902.variants.szekeres_lower :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (tournamentDominationNumber n : ℝ) ≥ C * (n : ℝ) * 2 ^ n := by
  sorry

end Erdos902
