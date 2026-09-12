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
# Erdős Problem 1087

*References:*
- [erdosproblems.com/1087](https://www.erdosproblems.com/1087)
- [ErPu71] Erdős, Paul and Purdy, George, *Some extremal problems in geometry*. J. Combinatorial
  Theory Ser. A (1971), 246--252.
- [Er75f] Erdős, P., *On some problems of elementary and combinatorial geometry*. Ann. Mat. Pura
  Appl. (4) (1975), 99--108.
-/

open Filter Real
open scoped EuclideanGeometry Asymptotics

namespace Erdos1087

/--
A 4-point set is degenerate if some pairwise distance occurs more than once, equivalently if it
determines fewer than six distinct distances.
-/
def IsDegenerateFourSet (S : Finset ℝ²) : Prop :=
  S.card = 4 ∧ distinctDistances S < 6

/-- The number of degenerate 4-point subsets of a finite point set in the plane. -/
noncomputable def degenerateFourSetCount (P : Finset ℝ²) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 4).filter IsDegenerateFourSet).card

/--
$f(n)$ is the least number such that every set of $n$ points in $\mathbb{R}^2$ contains at most
$f(n)$ degenerate 4-point subsets.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ P : Finset ℝ², P.card = n → degenerateFourSetCount P ≤ m}

@[category test, AMS 52]
theorem degenerateFourSetCount_empty :
    degenerateFourSetCount (∅ : Finset ℝ²) = 0 := by
  simp [degenerateFourSetCount, IsDegenerateFourSet]

@[category test, AMS 52]
theorem degenerateFourSetCount_eq_zero_of_card_lt_four {P : Finset ℝ²} (hP : P.card < 4) :
    degenerateFourSetCount P = 0 := by
  simp [degenerateFourSetCount, Finset.powersetCard_eq_empty.2 hP]

@[category test, AMS 52]
theorem f_eq_zero_of_lt_four {n : ℕ} (hn : n < 4) : f n = 0 := by
  refine Nat.eq_zero_of_le_zero (csInf_le (OrderBot.bddBelow _) ?_)
  intro P hP
  exact (degenerateFourSetCount_eq_zero_of_card_lt_four (hP ▸ hn)).le

/--
Let $f(n)$ be minimal such that every set of $n$ points in $\mathbb{R}^2$ contains at most $f(n)$
many sets of four points which are degenerate in the sense that some pair are the same distance
apart. Estimate $f(n)$ - in particular, is it true that $f(n)\leq n^{3+o(1)}$?
-/
@[category research open, AMS 52]
theorem erdos_1087 : answer(sorry) ↔
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (3 + o n) := by
  sorry

/-- Erdős and Purdy [ErPu71] proved $n^3\log n \ll f(n)$. -/
@[category research solved, AMS 52]
theorem erdos_1087.variants.lower_bound :
    (fun n : ℕ => (n : ℝ) ^ 3 * log n) ≪ fun n : ℕ => (f n : ℝ) := by
  sorry

/-- Erdős and Purdy [ErPu71] proved $f(n) \ll n^{7/2}$. -/
@[category research solved, AMS 52]
theorem erdos_1087.variants.upper_bound :
    (fun n : ℕ => (f n : ℝ)) ≪ fun n : ℕ => (n : ℝ) ^ (7 / 2 : ℝ) := by
  sorry

end Erdos1087
