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
# Erdős Problem 55

*References:*
- [erdosproblems.com/55](https://www.erdosproblems.com/55)
- [BuEr85] Burr, S. A. and Erdős, P., *A Ramsey-type property in additive number theory*.
  Glasgow Math. J. (1985), 5-10.
- [CFP21] Conlon, D., Fox, J., and Pham, H. T., *Subset sums, completeness and colorings*.
  arXiv:2104.14766 (2021).
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
-/

@[expose] public section

open Filter

namespace Erdos55

/--
A set $A \subseteq \mathbb{N}$ is *Ramsey $r$-complete* if, for every $r$-colouring of $A$,
every sufficiently large integer is a sum of distinct elements of $A$ of the same colour.
-/
def IsRamseyComplete (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ c : ℕ → Fin r, ∀ᶠ n in atTop, ∃ i, n ∈ subsetSums (A ∩ c ⁻¹' {i})

/-- A superset of a Ramsey $r$-complete set is Ramsey $r$-complete. -/
@[category API, AMS 5 11]
theorem IsRamseyComplete.mono {r : ℕ} {A B : Set ℕ} (hAB : A ⊆ B)
    (hA : IsRamseyComplete r A) : IsRamseyComplete r B := by
  intro c
  filter_upwards [hA c] with n ⟨i, hi⟩
  exact ⟨i, subsetSums_mono (Set.inter_subset_inter_left _ hAB) hi⟩

/-- A set is Ramsey $1$-complete if and only if it is complete. -/
@[category API, AMS 5 11]
theorem isRamseyComplete_one_iff {A : Set ℕ} : IsRamseyComplete 1 A ↔ IsAddComplete A := by
  have h (c : ℕ → Fin 1) (i : Fin 1) : A ∩ c ⁻¹' {i} = A := by
    ext n
    simp [Subsingleton.elim (c n) i]
  refine ⟨fun hA => ?_, fun hA c => ?_⟩
  · filter_upwards [hA 0] with n ⟨i, hi⟩
    rwa [h] at hi
  · filter_upwards [hA] with n hn
    exact ⟨0, by rwa [h]⟩

/--
A set of integers $A$ is Ramsey $r$-complete if, whenever $A$ is $r$-coloured, all sufficiently
large integers can be written as a monochromatic sum of elements of $A$. Prove any non-trivial
bounds about the growth rate of such an $A$ for $r > 2$.

Solved by Conlon, Fox, and Pham [CFP21]. For every $r \geq 2$ there is a Ramsey $r$-complete
$A$ with $|A \cap \{1, \ldots, N\}| \ll r (\log N)^2$ for all large $N$. This is best possible:
there is some $c > 0$ such that no $A$ with $|A \cap \{1, \ldots, N\}| \leq c r (\log N)^2$ for
all large $N$ is Ramsey $r$-complete.
-/
@[category research solved, AMS 5 11]
theorem erdos_55 :
    (∃ C : ℝ, ∀ r : ℕ, 2 ≤ r → ∃ A : Set ℕ, IsRamseyComplete r A ∧
      ∀ᶠ N : ℕ in atTop, ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ C * r * Real.log N ^ 2) ∧
    (∃ c > (0 : ℝ), ∀ r : ℕ, 2 ≤ r → ∀ A : Set ℕ,
      (∀ᶠ N : ℕ in atTop, ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ c * r * Real.log N ^ 2) →
        ¬ IsRamseyComplete r A) := by
  sorry

/--
Burr and Erdős [BuEr85] showed that there is some $c > 0$ such that no Ramsey $2$-complete $A$
satisfies $|A \cap \{1, \ldots, N\}| \leq c (\log N)^2$ for all large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_55.variants.two_lower :
    ∃ c > (0 : ℝ), ∀ A : Set ℕ,
      (∀ᶠ N : ℕ in atTop, ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ c * Real.log N ^ 2) →
        ¬ IsRamseyComplete 2 A := by
  sorry

/--
Burr and Erdős [BuEr85] constructed a Ramsey $2$-complete $A$ such that
$|A \cap \{1, \ldots, N\}| \ll (\log N)^3$ for all large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_55.variants.two_upper :
    ∃ C : ℝ, ∃ A : Set ℕ, IsRamseyComplete 2 A ∧
      ∀ᶠ N : ℕ in atTop, ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ C * Real.log N ^ 3 := by
  sorry

/--
Burr showed that, for every $r, k \geq 1$, the set of $k$th powers of positive integers is
Ramsey $r$-complete.
-/
@[category research solved, AMS 5 11]
theorem erdos_55.variants.powers (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    IsRamseyComplete r (Set.range fun n : ℕ => (n + 1) ^ k) := by
  sorry

end Erdos55
