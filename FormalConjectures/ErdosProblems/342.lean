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
# Erdős Problem 342

*References:*
- [erdosproblems.com/342](https://www.erdosproblems.com/342)
- [Ben Green's Open Problem 7](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.7)
- [OEIS A002858](https://oeis.org/A002858)
- [Gu04] Guy, Richard K., *Unsolved problems in number theory* (2004), xviii+437.
-/

open Nat Set Filter
open scoped Topology

namespace Erdos342

/-- `UniqueUlamSum a n m` means that $m$ has a unique representation as $a(i) + a(j)$
with $i < j < n$. -/
def UniqueUlamSum (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 < n ∧ m = a p.1 + a p.2

/-- `IsUlamSequence a` means that $a$ is the Ulam sequence (OEIS A002858):
$a(0) = 1$, $a(1) = 2$, and for each $n \geq 2$, $a(n)$ is the least integer
greater than $a(n-1)$ that has a unique representation as $a(i) + a(j)$
with $i < j < n$. -/
def IsUlamSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    UniqueUlamSum a n (a n) ∧
    ∀ m, a (n - 1) < m → m < a n → ¬ UniqueUlamSum a n m

/-- $a(0) = 1$ by definition. -/
@[category test, AMS 5 11 40]
theorem erdos_342.test.a0 : ∀ a : ℕ → ℕ, IsUlamSequence a → a 0 = 1 := by
  intro a ⟨ha0, _, _⟩; exact ha0

/-- $a(1) = 2$ by definition. -/
@[category test, AMS 5 11 40]
theorem erdos_342.test.a1 : ∀ a : ℕ → ℕ, IsUlamSequence a → a 1 = 2 := by
  intro a ⟨_, ha1, _⟩; exact ha1

/-- $a(2) = 3$: the only pair $(i,j)$ with $i < j < 2$ is $(0,1)$, giving $1 + 2 = 3$. -/
@[category test, AMS 5 11 40]
theorem erdos_342.test.a2 : ∀ a : ℕ → ℕ, IsUlamSequence a → a 2 = 3 := by
  intro a ⟨ha0, ha1, ha⟩
  obtain ⟨_, ⟨⟨i, j⟩, ⟨hij, hj, hsum⟩, _⟩, _⟩ := ha 2 (by omega)
  interval_cases j <;> simp_all only [lt_one_iff, not_lt_zero']

/-- $a(3) = 4$: among sums $> 3$ with a unique representation from $\{1,2,3\}$,
the smallest is $4 = 1 + 3$. The candidate $5 = 2 + 3$ is ruled out by minimality since
$4$ has a unique representation. -/
@[category test, AMS 05 11 40]
theorem erdos_342.test.a3 : ∀ a : ℕ → ℕ, IsUlamSequence a → a 3 = 4 := by
  intro a ⟨ha0, ha1, ha⟩
  have ha2 := erdos_342.test.a2 a ⟨ha0, ha1, ha⟩
  obtain ⟨hinc, ⟨⟨i, j⟩, ⟨hij, hj, hsum⟩, _⟩, hmin⟩ := ha 3 (by omega)
  simp only [show (3 : ℕ) - 1 = 2 from rfl] at hinc hmin
  -- hinc : a 2 < a 3, hmin : ∀ m, a 2 < m → m < a 3 → ¬UniqueUlamSum a 3 m
  -- hsum : a 3 = a i + a j, hij : i < j, hj : j < 3
  -- Enumerate j ∈ {0, 1, 2}
  interval_cases j
  · -- j = 0: i < 0 impossible
    omega
  · -- j = 1: i = 0, so a 3 = a 0 + a 1 = 1 + 2 = 3, but a 3 > a 2 = 3
    have hi : i = 0 := by omega
    subst hi; rw [ha0, ha1] at hsum; rw [ha2] at hinc; omega
  · -- j = 2
    interval_cases i
    · -- i = 0: a 3 = a 0 + a 2 = 1 + 3 = 4
      rw [ha0, ha2] at hsum; exact hsum
    · -- i = 1: a 3 = a 1 + a 2 = 2 + 3 = 5
      rw [ha1, ha2] at hsum
      -- hsum : a 3 = 5. Use minimality: m = 4 has unique sum, contradiction.
      exfalso
      have h4 := hmin 4 (by rw [ha2]; omega) (by omega)
      apply h4
      -- Goal: UniqueUlamSum a 3 4, i.e. ∃! (p : ℕ × ℕ), p.1 < p.2 ∧ p.2 < 3 ∧ 4 = a p.1 + a p.2
      -- Witness: (0, 2) since a 0 + a 2 = 1 + 3 = 4
      refine ⟨⟨0, 2⟩, ⟨by omega, by omega, by rw [ha0, ha2]⟩, ?_⟩
      -- Uniqueness: check all pairs (i', j') with i' < j' < 3
      rintro ⟨i', j'⟩ ⟨hij', hj', hsum'⟩
      simp only [Prod.mk.injEq]
      interval_cases j'
      · omega
      · interval_cases i'
        · rw [ha0, ha1] at hsum'; omega
      · interval_cases i'
        · rw [ha0, ha2] at hsum'; constructor <;> omega
        · rw [ha1, ha2] at hsum'; omega

/--
Do infinitely many pairs $(a, a+2)$ occur in Ulam's sequence? -/
@[category research open, AMS 05 11 40]
theorem erdos_342.parts.i :
    answer(sorry) ↔
      ∀ a : ℕ → ℕ, IsUlamSequence a →
        Set.Infinite {n : ℕ | ∃ m, a m = a n + 2} := by
  sorry

/--
Does Ulam's sequence eventually have periodic differences? That is, is $a(n+1) - a(n)$ eventually periodic?
-/
@[category research open, AMS 05 11 40]
theorem erdos_342.parts.ii :
    answer(sorry) ↔
      ∀ a : ℕ → ℕ, IsUlamSequence a →
        let d (n : ℕ) : ℤ := a (n + 1) - a n
        ∃ p > 0, ∀ᶠ m in atTop, d (m + p) = d m := by
  sorry

/--
Part (iii), is the density of the sequence 0?
-/
@[category research open, AMS 05 11 40]
theorem erdos_342.parts.iii :
    answer(sorry) ↔
      ∀ a : ℕ → ℕ, IsUlamSequence a →
        Set.upperDensity (Set.range a) = 0 := by
  sorry

end Erdos342
