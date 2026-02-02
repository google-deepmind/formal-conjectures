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

*Reference:*
* [erdosproblems.com/18](https://www.erdosproblems.com/18)
* [ErGr80] Erdős, P. and Graham, R. L. (1980). Old and New Problems and Results in Combinatorial Number
Theory. Monographies de L'Enseignement Mathématique, 28. Université de Genève. (See the
sections on Egyptian fractions or practical numbers).
* [Vo85] Vose, Michael D., Egyptian fractions. Bull. London Math. Soc. (1985), 21-24.
-/

open Filter Asymptotics Real

namespace Erdos18

/-- For a practical number $n$, $h(n)$ is the maximum over all $1 ≤ m ≤ n$ of
the minimum number of divisors of $n$ needed to represent $m$ as a sum of
distinct divisors. -/
noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/-! ### Examples for `practicalH` -/

/-- $h(1) = 1$: we need the single divisor {1} to represent 1. -/
@[category test, AMS 11]
theorem practicalH_one : practicalH 1 = 1 := by
  simp only [practicalH, Finset.Icc_self, Finset.sup_singleton]
  refine le_antisymm (Nat.sInf_le ⟨{1}, by simp [Nat.divisors_one], rfl, {1}, rfl.subset, by simp⟩)
    (le_csInf ⟨1, {1}, by simp [Nat.divisors_one], rfl, {1}, rfl.subset, by simp⟩ ?_)
  intro k ⟨D, _, hD_card, B, hB_sub, hB_sum⟩
  exact Nat.one_le_iff_ne_zero.mpr (hD_card ▸ Finset.card_ne_zero.mpr
    ((Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hB_sum).mono hB_sub))

/-- $h(2) = 1$: divisors are {1, 2}, each of m=1,2 needs only 1 divisor. -/
@[category test, AMS 11]
theorem practicalH_two : practicalH 2 = 1 := by
  simp only [practicalH, (by decide : Finset.Icc 1 2 = ({1, 2} : Finset ℕ)),
    (by decide : Nat.divisors 2 = ({1, 2} : Finset ℕ)), Finset.sup_insert, Finset.sup_singleton]
  have h1 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2} ∧ D.card = k ∧ 1 ∈ subsetSums D} = 1 :=
    le_antisymm (Nat.sInf_le ⟨{1}, by simp, rfl, {1}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {1}, by simp, rfl, {1}, rfl.subset, by simp⟩ fun k ⟨D, _, hD, B, hB, hm⟩ =>
        hD ▸ Finset.one_le_card.mpr ((Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hm).mono hB))
  have h2 : sInf {k | ∃ D : Finset ℕ, D ⊆ {1, 2} ∧ D.card = k ∧ 2 ∈ subsetSums D} = 1 :=
    le_antisymm (Nat.sInf_le ⟨{2}, by simp, rfl, {2}, rfl.subset, by simp⟩)
      (le_csInf ⟨1, {2}, by simp, rfl, {2}, rfl.subset, by simp⟩ fun k ⟨D, _, hD, B, hB, hm⟩ =>
        hD ▸ Finset.one_le_card.mpr ((Finset.nonempty_iff_ne_empty.mpr fun h => by simp [h] at hm).mono hB))
  simp [h1, h2]

/-- $h(6) = 2$: divisors are {1, 2, 3, 6}. The hardest m to represent is
m=4 or m=5, each requiring 2 divisors: 4=1+3, 5=2+3. -/
@[category test, AMS 11]
theorem practicalH_six : practicalH 6 = 2 := by
  sorry

/-- $h(12) = 3$: divisors are {1, 2, 3, 4, 6, 12}. The hardest m is
m=11, requiring 3 divisors: 11=1+4+6. -/
@[category test, AMS 11]
theorem practicalH_twelve : practicalH 12 = 3 := by
  sorry

/-- For any practical number $n$, $h(n) ≤ number of divisors of $n$. -/
@[category test, AMS 11]
theorem practicalH_le_divisors (n : ℕ) (hn : Nat.IsPractical n) :
    practicalH n ≤ n.divisors.card := by
  simp only [practicalH, Finset.sup_le_iff, Finset.mem_Icc]
  exact fun m ⟨_, hm⟩ => Nat.sInf_le ⟨n.divisors, Finset.Subset.refl _, rfl, hn m hm⟩

/-- $h(n!)$ is well-defined since $n!$ is practical for $n ≥ 1$. -/
@[category undergraduate, AMS 11]
theorem factorial_isPractical (n : ℕ) (hn : 1 ≤ n) : Nat.IsPractical n.factorial := by
  sorry

/-! ### Erdős's Conjectures -/

/--
**Conjecture 1.**
Are there infinitely many practical numbers $m$ such that $h(m) < (\log \log m)^{O(1)}$?

More precisely: does there exist a constant $C > 0$ such that for all sufficiently large
practical numbers $m$, we have $h(m) < (\log \log m)^C$?
-/
@[category research open, AMS 11]
theorem erdos_18a : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in atTop, Nat.IsPractical m →
      (practicalH m : ℝ) < (log (log m)) ^ C := by
  sorry

/--
**Conjecture 2.**
Is it true that $h(n!) < n^{o(1)}$? That is, for all $\varepsilon > 0$,
is $h(n!) < n^\varepsilon$ for sufficiently large $n$?
-/
@[category research open, AMS 11]
theorem erdos_18b : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (practicalH n.factorial : ℝ) < (n : ℝ) ^ ε := by
  sorry

/--
**Conjecture 3.**
Or perhaps even $h(n!) < (\log n)^{O(1)}$?

Erdős offered \$250 for a proof or disproof.
-/
@[category research open, AMS 11]
theorem erdos_18c : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (practicalH n.factorial : ℝ) < (log n) ^ C := by
  sorry

/--
**Erdős's Theorem.**
Erdős proved that $h(n!) < n$ for all $n \ge 1$.
-/
@[category research solved, AMS 11]
theorem erdos_18_upper_bound :
    ∀ᶠ n : ℕ in atTop, practicalH (Nat.factorial n) < n := by
  sorry

/--
**Vose's Theorem.**
Vose proved the existence of infinitely many practical numbers $m$ such that
$h(m) \ll (\log m)^{1/2}$. This gives a positive answer to a weaker form of Conjecture 1.
-/
@[category research solved, AMS 11]
theorem erdos_18_vose :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in atTop, Nat.IsPractical m →
      (practicalH m : ℝ) < C * (log m) ^ (1 / 2 : ℝ) := by
  sorry

end Erdos18
