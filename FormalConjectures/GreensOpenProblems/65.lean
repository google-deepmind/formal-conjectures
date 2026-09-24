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
module

public import FormalConjecturesUtil

/-!
# Ben Green's Open Problem 65

*References:*
- [Gr24] [Ben Green's Open Problem 65](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.65)
- [Gr22] Green, Ben. *On Sárközy's theorem for shifted primes*. [arXiv:2206.08001](https://arxiv.org/abs/2206.08001), 2022.
- [Ru84] Ruzsa, Imre Z. *Difference sets without squares*. Period. Math. Hungar. 15 (1984), 205–229.
-/

@[expose] public section

open Finset Filter
open scoped Pointwise

namespace Green65

/-- An integer is a nonzero square if it is the square of a nonzero natural number. -/
def IsNonzeroSquare (d : ℤ) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ d = (n : ℤ) ^ 2

/-- An integer is one less than a prime. -/
def IsPrimeMinusOne (d : ℤ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ d = (p : ℤ) - 1

/-- The interval $[N] = \{1, \ldots, N\}$, viewed as a finite set of integers. -/
def interval (N : ℕ) : Finset ℤ :=
  Icc (1 : ℤ) (N : ℤ)

/--
There is a fixed density exponent $c \in (0,1)$ such that every sufficiently large subset
$A \subseteq [N]$ with $|A| \geq N^{1-c}$ has a difference satisfying $P$.

We quantify over sufficiently large $N$, since the literal statement for every $N > 0$ is false
for nonzero squares: $A = \{1\} \subseteq [1]$ has $|A| = 1 = 1^{1-c}$ and $A - A = \{0\}$.
-/
def LargeDifferencePattern (P : ℤ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
    A ⊆ interval N →
      (N : ℝ) ^ (1 - c) ≤ (A.card : ℝ) →
        ∃ d ∈ A - A, P d

/-- Without "sufficiently large $N$" the square question is false for every $c$:
$A = \{1\} \subseteq [1]$ has $|A| = 1 = 1^{1-c}$ and $A - A = \{0\}$. -/
@[category test, AMS 5 11]
theorem green_65.test.not_forall_N :
    ¬ ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ N : ℕ, ∀ A : Finset ℤ,
      A ⊆ interval N → (N : ℝ) ^ (1 - c) ≤ (A.card : ℝ) →
        ∃ d ∈ A - A, IsNonzeroSquare d := by
  rintro ⟨c, -, -, h⟩
  obtain ⟨d, hd, n, hn, hdn⟩ :=
    h 1 {1} (by decide) (by norm_num [Real.one_rpow])
  rcases mem_sub.mp hd with ⟨a, ha, b, hb, rfl⟩
  simp only [mem_singleton] at ha hb
  subst ha
  subst hb
  rw [eq_comm] at hdn
  simp at hdn
  exact hn hdn

/-- Consecutive integers differ by $1^2$ and by $2 - 1$. -/
@[category test, AMS 5 11]
theorem green_65.test.consecutive {A : Finset ℤ} {a : ℤ}
    (ha : a ∈ A) (ha1 : a + 1 ∈ A) :
    (∃ d ∈ A - A, IsNonzeroSquare d) ∧ (∃ d ∈ A - A, IsPrimeMinusOne d) := by
  have hmem : (1 : ℤ) ∈ A - A := mem_sub.mpr ⟨a + 1, ha1, a, ha, by ring⟩
  exact ⟨⟨1, hmem, 1, one_ne_zero, by norm_num⟩,
    ⟨1, hmem, 2, Nat.prime_two, by norm_num⟩⟩

/--
Is there $c > 0$ such that every sufficiently large subset $A \subseteq [N]$ of size at least
$N^{1-c}$ has a difference that is a nonzero square?
-/
@[category research open, AMS 5 11]
theorem green_65 :
    answer(sorry) ↔ LargeDifferencePattern IsNonzeroSquare := by
  sorry

/--
Green asks the analogous question with a nonzero square replaced by $p - 1$ for a prime $p$.
Green [Gr22, Theorem 1.1] proved a power-saving bound $|A| \ll N^{1-c}$.
-/
@[category research solved, AMS 5 11]
theorem green_65.variants.prime_minus_one :
    answer(True) ↔ LargeDifferencePattern IsPrimeMinusOne := by
  sorry

/--
Ruzsa [Ru84] constructed subsets of $[N]$ of size $N^{1-c}$ with no square difference, for some
$c > 0$. Green records that no exponent $c > 0.267$ can work for the square problem.
-/
@[category research solved, AMS 5 11]
theorem green_65.variants.ruzsa_obstruction :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ᶠ N : ℕ in atTop, ∃ A ⊆ interval N,
      (N : ℝ) ^ (1 - c) ≤ (A.card : ℝ) ∧ ¬ ∃ d ∈ A - A, IsNonzeroSquare d := by
  sorry

/--
Green also asks the following presumably easier question: if $A \subset [N]$ has size $N^{1-c}$,
does the $100$-fold difference set $100A - 100A$ contain a nonzero square?
-/
@[category research open, AMS 5 11]
theorem green_65.variants.hundredfold :
    answer(sorry) ↔
      ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
        A ⊆ interval N →
          (N : ℝ) ^ (1 - c) ≤ (A.card : ℝ) →
            ∃ d ∈ ((100 : ℕ) • A) - ((100 : ℕ) • A), IsNonzeroSquare d := by
  sorry

end Green65
