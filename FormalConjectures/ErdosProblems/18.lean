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

import FormalConjectures.Util.ProblemImports
import FormalConjecturesForMathlib.NumberTheory.PracticalNumbers

/-!
# Erdős Problem 18

*Reference:* [erdosproblems.com/18](https://www.erdosproblems.com/18)

For a practical number $m$, let $h(m)$ be the minimum number of divisors of $m$
needed to represent every positive integer $1 \le k \le m$ as a sum of distinct divisors.

Erdős proved that $h(n!) < n$.
-/

open Filter Asymptotics Real

namespace Erdos18

/-- The set of subset sums of a finite set of natural numbers. -/
def subsetSums (D : Finset ℕ) : Set ℕ :=
  {m | ∃ B : Finset ℕ, B ⊆ D ∧ m = ∑ i ∈ B, i}

/-- For a practical number `n`, `practicalH n` is the minimum number of divisors of `n` needed
to represent all positive integers up to `n` as sums of distinct divisors. -/
noncomputable def practicalH (n : ℕ) : ℕ :=
  sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧
    ∀ m, 0 < m → m ≤ n → m ∈ subsetSums D}

/-! ### Examples for `practicalH` -/

/-- h(1) = 1: we need the single divisor {1} to represent 1. -/
@[category test, AMS 11]
theorem practicalH_one : practicalH 1 = 1 := by
  unfold practicalH
  apply le_antisymm
  · -- sInf S ≤ 1
    apply Nat.sInf_le
    refine ⟨{1}, ?_, ?_, ?_⟩
    · simp [Nat.divisors_one]
    · simp
    · intro m hm hle
      interval_cases m
      exact ⟨{1}, Finset.Subset.refl _, by simp⟩
  · -- 1 ≤ sInf S
    apply le_csInf
    · -- nonempty
      refine ⟨1, {1}, ?_, ?_, ?_⟩
      · simp [Nat.divisors_one]
      · simp
      · intro m hm hle
        interval_cases m
        exact ⟨{1}, Finset.Subset.refl _, by simp⟩
    · -- lower bound
      intro k ⟨D, _, hD_card, hD_covers⟩
      have h1 : 1 ∈ subsetSums D := hD_covers 1 (by omega) (by omega)
      obtain ⟨B, hB_sub, hB_sum⟩ := h1
      have hB_ne : B.Nonempty := by
        by_contra h
        simp only [Finset.not_nonempty_iff_eq_empty] at h
        simp [h] at hB_sum
      have hD_ne : D.Nonempty := hB_ne.mono hB_sub
      have : D.card ≥ 1 := Finset.Nonempty.card_pos hD_ne
      omega

/-- h(2) = 2: divisors are {1, 2}, we need both to represent 1 and 2. -/
@[category test, AMS 11]
theorem practicalH_two : practicalH 2 = 2 := by
  sorry

/-- h(6) = 3: divisors are {1, 2, 3, 6}, but {1, 2, 3} suffices:
1=1, 2=2, 3=3, 4=1+3, 5=2+3, 6=1+2+3. -/
@[category test, AMS 11]
theorem practicalH_six : practicalH 6 = 3 := by
  sorry

/-- h(12) = 4: divisors are {1, 2, 3, 4, 6, 12}, but {1, 2, 3, 6} suffices. -/
@[category test, AMS 11]
theorem practicalH_twelve : practicalH 12 = 4 := by
  sorry

/-- For any practical number n, h(n) ≤ number of divisors of n. -/
@[category test, AMS 11]
theorem practicalH_le_divisors (n : ℕ) (hn : Nat.IsPractical n) :
    practicalH n ≤ n.divisors.card := by
  sorry

/-- h(n!) is well-defined since n! is practical for n ≥ 1. -/
@[category test, AMS 11]
theorem factorial_isPractical (n : ℕ) (hn : 1 ≤ n) : Nat.IsPractical n.factorial := by
  sorry

/-! ### Erdős's Conjectures -/

/--
**Erdős Problem 18, Conjecture 1.**
Are there infinitely many practical numbers $m$ such that $h(m) < (\log \log m)^{O(1)}$?

More precisely: does there exist a constant $C > 0$ such that
$\{m \mid m \text{ is practical and } h(m) < (\log \log m)^C\}$ is infinite?
-/
@[category research open, AMS 11]
theorem erdos_18a : answer(sorry) ↔
    ∃ C : ℝ, 0 < C ∧ {m : ℕ | Nat.IsPractical m ∧
      (practicalH m : ℝ) < (log (log m)) ^ C}.Infinite := by
  sorry

/--
**Erdős Problem 18, Conjecture 2.**
Is it true that $h(n!) < n^{o(1)}$? That is, for all $\varepsilon > 0$,
is $h(n!) < n^\varepsilon$ for sufficiently large $n$?
-/
@[category research open, AMS 11]
theorem erdos_18b : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (practicalH n.factorial : ℝ) < (n : ℝ) ^ ε := by
  sorry

/--
**Erdős Problem 18, Conjecture 3.**
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

*Reference:*
Erdős, P. and Graham, R. L. (1980). Old and New Problems and Results in Combinatorial Number
Theory. Monographies de L'Enseignement Mathématique, 28. Université de Genève. (See the
sections on Egyptian fractions or practical numbers).
-/
@[category research solved, AMS 11]
theorem erdos_18_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    practicalH n.factorial < n := by
  sorry

/--
**Vose's Theorem.**
Vose proved the existence of infinitely many practical numbers $m$ such that
$h(m) \ll (\log m)^{1/2}$.

This gives a positive answer to a weaker form of Conjecture 1.

*Reference:* Vose, Michael D., Egyptian fractions. Bull. London Math. Soc. (1985), 21-24.
-/
@[category research solved, AMS 11]
theorem erdos_18_vose :
    ∃ C : ℝ, {m : ℕ | Nat.IsPractical m ∧
      (practicalH m : ℝ) < C * (log m) ^ (1 / 2 : ℝ)}.Infinite := by
  sorry

end Erdos18
