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
# Erdős Problem 635

*References:*
- [erdosproblems.com/635](https://www.erdosproblems.com/635)
- [Gu83] Guy, R., _A Miscellany of Erdős Problems_. Amer. Math. Monthly (1983), 118–120.
- [Ru99] Ruzsa, I., _Erdős and the Integers_. J. Number Theory (1999), 115–163.
- [El79] Elliott, P. D. T. A., _Probabilistic number theory. I_. Springer-Verlag (1979).
- [Discussion](https://www.erdosproblems.com/forum/thread/635)
-/

@[expose] public section

namespace Erdos635

open Finset

/-- No difference of size at least `t` between elements of `A` divides its larger endpoint. -/
def IsAdmissible (t : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, t ≤ b - a → ¬ (b - a) ∣ b

open scoped Classical in
/-- The largest size of an admissible subset of $\{1,\ldots,N\}$. -/
noncomputable def maxCard (t N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (IsAdmissible t)).sup Finset.card

/-- Every admissible subset has size at most `maxCard`. -/
@[category API, AMS 5 11]
theorem card_le_maxCard {t N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (h : IsAdmissible t A) : A.card ≤ maxCard t N := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hA, h⟩)

/-- The extremal size is bounded by the size of the ambient interval. -/
@[category API, AMS 5 11]
theorem maxCard_le (t N : ℕ) : maxCard t N ≤ N := by
  classical
  apply Finset.sup_le
  intro A hA
  have h := Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)
  simpa using h

/-- An admissible set for $t=1$ contains at most $\lfloor(N+1)/2\rfloor$ elements. -/
@[category API, AMS 5 11]
theorem card_le_half {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 N) (h : IsAdmissible 1 A) : A.card ≤ (N + 1) / 2 := by
  have hinj : Set.InjOn (fun a : ℕ ↦ (a + 1) / 2) A := by
    intro a ha b hb hab
    dsimp only at hab
    have hab' : a = b ∨ a + 1 = b ∨ b + 1 = a := by omega
    rcases hab' with rfl | hab' | hab'
    · rfl
    · have hh := h a ha b hb (by omega)
      have hdiff : b - a = 1 := by omega
      simp [hdiff] at hh
    · have hh := h b hb a ha (by omega)
      have hdiff : a - b = 1 := by omega
      simp [hdiff] at hh
  have hsub : A.image (fun a ↦ (a + 1) / 2) ⊆ Icc 1 ((N + 1) / 2) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    have haN := mem_Icc.mp (hA ha)
    simp only [mem_Icc]
    omega
  calc
    A.card = (A.image (fun a ↦ (a + 1) / 2)).card := (card_image_of_injOn hinj).symm
    _ ≤ (Icc 1 ((N + 1) / 2)).card := card_le_card hsub
    _ = (N + 1) / 2 := by simp

/-- The odd numbers give an admissible set of size $\lfloor(N+1)/2\rfloor$. -/
@[category API, AMS 5 11]
theorem exists_admissible_card_half (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ IsAdmissible 1 A ∧ A.card = (N + 1) / 2 := by
  refine ⟨(range ((N + 1) / 2)).image (fun k ↦ 2 * k + 1), ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨k, hk, rfl⟩ := mem_image.mp ha
    have hk' := mem_range.mp hk
    simp only [mem_Icc]
    omega
  · intro a ha b hb hpos hdiv
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
    have hdiff : (2 * j + 1) - (2 * i + 1) = 2 * (j - i) := by omega
    have heven : 2 ∣ (2 * j + 1) := dvd_trans (by rw [hdiff]; exact dvd_mul_right _ _) hdiv
    obtain ⟨k, hk⟩ := heven
    omega
  · rw [card_image_of_injective _ (by intro a b hab; dsimp only at hab; omega), card_range]

/--
Let $t\geq 1$ and $A\subseteq \{1,\ldots,N\}$ be such that whenever $a,b\in A$ with
$b-a\geq t$ we have $b-a\nmid b$. How large can $\lvert A\rvert$ be?
-/
@[question value, category research open, AMS 5 11]
theorem erdos_635.parts.i : (fun (t : ℕ+) (N : ℕ) ↦ maxCard t N) = answer(sorry) := by
  sorry

/--
Is it true that $\lvert A\rvert \leq (\frac{1}{2}+o_t(1))N$?

The second question has been resolved in the affirmative by ChatGPT-5.2 (prompted by Leeham);
Tao has since observed that a positive answer also follows fairly quickly from an inequality
due to Elliott [El79].
-/
@[question, category research solved, AMS 5 11]
theorem erdos_635.parts.ii : answer(True) ↔
    ∀ t : ℕ, 1 ≤ t → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → IsAdmissible t A →
        (A.card : ℝ) ≤ (1 / 2 + ε) * N := by
  sorry

/--
Erdős observes that when $t=1$ the maximum possible is
$\lvert A\rvert=\lfloor\frac{N+1}{2}\rfloor$, achieved by taking $A$ to be all odd numbers
in $\{1,\ldots,N\}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_635.variants.t_eq_one (N : ℕ) : maxCard 1 N = (N + 1) / 2 := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro A hA
    obtain ⟨hA, h⟩ := Finset.mem_filter.mp hA
    exact card_le_half (Finset.mem_powerset.mp hA) h
  · obtain ⟨A, hA, h, hcard⟩ := exists_admissible_card_half N
    exact hcard ▸ card_le_maxCard hA h

/--
Erdős observes that when $t=2$ there exists such an $A$ with
$\lvert A\rvert \geq \frac{N}{2}+c\log N$ for some constant $c>0$: take $A$ to be the union
of all odd numbers together with numbers of the shape $2^k$ with $k$ odd.
-/
@[category research solved, AMS 5 11]
theorem erdos_635.variants.logarithmic_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ IsAdmissible 2 A ∧
        (N : ℝ) / 2 + c * Real.log N ≤ A.card := by
  sorry

end Erdos635
