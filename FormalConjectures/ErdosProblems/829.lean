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
# Erdős Problem 829

*References:*
- [erdosproblems.com/829](https://www.erdosproblems.com/829)
- [Er83] Erdős, P. and Dudley, U., _Some remarks and problems in number theory related to the
  work of Euler_. Math. Mag. (1983), 292-298.
-/

open AdditiveCombinatorics Asymptotics Filter

namespace Erdos829

/-- The set of perfect cubes in $\mathbb{N}$. -/
def cubes : Set ℕ := {n | ∃ k, k ^ 3 = n}

/-- Membership in `cubes` can be witnessed by a bounded cube root, which makes it
decidable for concrete values. -/
@[category API, AMS 11]
lemma mem_cubes_iff (m : ℕ) : m ∈ cubes ↔ ∃ k, k < m + 1 ∧ k ^ 3 = m := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_, rfl⟩
    have : k ≤ k ^ 3 := Nat.le_self_pow (by norm_num) k
    omega
  · rintro ⟨k, _, rfl⟩
    exact ⟨k, rfl⟩

/--
**Erdős Problem 829 (open).**  Let $A \subseteq \mathbb{N}$ be the set of perfect cubes.  Is
it true that $(1_A \ast 1_A)(n) \ll (\log n)^{O(1)}$?  That is, does there exist a natural
number $C$ such that the number of representations of $n$ as a sum of two cubes is
$O((\log n)^C)$ as $n \to \infty$?
-/
@[category research open, AMS 11]
theorem erdos_829 :
    answer(sorry) ↔
      ∃ C : ℕ, (fun n : ℕ => (sumRep cubes n : ℝ)) =O[atTop]
        (fun n : ℕ => (Real.log n) ^ C) := by
  sorry

/-- There is exactly one ordered pair of cubes summing to $0$, namely $(0, 0)$. -/
@[category test, AMS 11]
theorem sumRep_cubes_zero : sumRep cubes 0 = 1 := by
  simp only [sumRep_def, mem_cubes_iff]
  decide

/-- The only ordered pair of cubes summing to $2$ is $(1, 1)$. -/
@[category test, AMS 11]
theorem sumRep_cubes_two : sumRep cubes 2 = 1 := by
  simp only [sumRep_def, mem_cubes_iff]
  decide

/-- The integer $3$ is not the sum of two cubes. -/
@[category test, AMS 11]
theorem sumRep_cubes_three : sumRep cubes 3 = 0 := by
  simp only [sumRep_def, mem_cubes_iff]
  decide

/-- The Hardy-Ramanujan taxicab number satisfies $1729 = 1^3 + 12^3 = 9^3 + 10^3$, giving
the four ordered representations $(1, 1728), (1728, 1), (729, 1000), (1000, 729)$. -/
@[category test, AMS 11]
theorem sumRep_cubes_taxicab : sumRep cubes 1729 = 4 := by
  simp only [sumRep_def, mem_cubes_iff]
  decide +native

namespace variants

/--
Mordell proved $\limsup_{n \to \infty} (1_A \ast 1_A)(n) = \infty$, where $A$ is the set of
perfect cubes.  Equivalently, the number of representations of $n$ as a sum of two cubes is
unbounded.
-/
@[category research solved, AMS 11]
theorem mordell : limsup (fun n : ℕ => (sumRep cubes n : ℕ∞)) atTop = (⊤ : ℕ∞) := by
  sorry

/--
Mahler proved $(1_A \ast 1_A)(n) \gg (\log n)^{1/4}$ for infinitely many $n$, where $A$ is
the set of perfect cubes.

[Ma35b] Mahler, K., _On the lattice points on curves of genus 1_. Proc. London Math. Soc.
  (2) (1935), 431-466.
-/
@[category research solved, AMS 11]
theorem mahler : ∃ C > (0 : ℝ),
    ∃ᶠ (n : ℕ) in atTop, C * (Real.log n) ^ ((1 : ℝ) / 4) ≤ (sumRep cubes n : ℝ) := by
  sorry

/--
Stewart improved Mahler's lower bound to $(1_A \ast 1_A)(n) \gg (\log n)^{11/13}$ for
infinitely many $n$, where $A$ is the set of perfect cubes.

[St08] Stewart, C. L., _Cubic Thue equations with many solutions_. Int. Math. Res. Not.
  IMRN (2008), Art. ID rnn040, 11.
-/
@[category research solved, AMS 11]
theorem stewart : ∃ C > (0 : ℝ),
    ∃ᶠ (n : ℕ) in atTop, C * (Real.log n) ^ ((11 : ℝ) / 13) ≤ (sumRep cubes n : ℝ) := by
  sorry

end variants

end Erdos829
