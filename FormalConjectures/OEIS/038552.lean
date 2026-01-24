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

open Polynomial

/-!
# **Conjectures associated with A038552**

A038552 lists the largest squarefree number $k$ such that the imaginary quadratic field
$\mathbb{Q}(\sqrt{-k})$ has class number $n$.

The conjectures state that:
1. All terms are congruent to $19 \pmod{24}$.
2. This is also the largest absolute value of negative fundamental discriminant $d$ for
   class number $n$. For even $n$, if $k$ is the largest odd number with $h(-k) = n$ and
   $k'$ is the largest even number with $h(-k') = n$, then $k > k'$.

*References:* [oeis.org/A038552](https://oeis.org/A038552)
-/

namespace OeisA038552

/-- The class number of the imaginary quadratic field $\mathbb{Q}(\sqrt{-k})$ equals $n$. -/
def HasClassNumber (k n : ℕ) : Prop :=
  ∃ (h : Irreducible (X ^ 2 + C (k : ℚ))),
  haveI := Fact.mk h
  NumberField.classNumber (AdjoinRoot (X ^ 2 + C (k : ℚ))) = n

/-- $k$ is the largest squarefree number such that $\mathbb{Q}(\sqrt{-k})$ has class number $n$.
This defines the $n$-th term of A038552. -/
def a (n k : ℕ) : Prop :=
  Squarefree k ∧ HasClassNumber k n ∧
  ∀ m, Squarefree m → HasClassNumber m n → m ≤ k

/-- An integer $d < 0$ is a negative fundamental discriminant if either:
- $d \equiv 1 \pmod 4$ and $d$ is squarefree, or
- $d = 4m$ where $m \equiv 2$ or $3 \pmod 4$ and $m$ is squarefree. -/
def IsNegFundamentalDiscriminant (d : ℤ) : Prop :=
  d < 0 ∧ ((d % 4 = 1 ∧ Squarefree d) ∨
           (∃ m : ℤ, d = 4 * m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ Squarefree m))

/-- The class number of the quadratic field with discriminant $d$. -/
noncomputable def classNumberOfDiscriminant (d : ℤ) : ℕ :=
  haveI := Classical.dec (Irreducible (X ^ 2 - C (d : ℚ)))
  if h : Irreducible (X ^ 2 - C (d : ℚ)) then
    haveI := Fact.mk h
    NumberField.classNumber (AdjoinRoot (X ^ 2 - C (d : ℚ)))
  else 0

/-- $|d|$ is the largest absolute value among negative fundamental discriminants
with class number $n$. -/
def IsLargestNegFundDiscForClassNumber (n : ℕ) (absD : ℕ) : Prop :=
  IsNegFundamentalDiscriminant (-(absD : ℤ)) ∧
  classNumberOfDiscriminant (-(absD : ℤ)) = n ∧
  ∀ d : ℤ, IsNegFundamentalDiscriminant d → classNumberOfDiscriminant d = n → d.natAbs ≤ absD

/-- The Stark-Heegner theorem implies that the squarefree $k > 0$ such that
$\mathbb{Q}(\sqrt{-k})$ has class number $1$ are exactly $\{1, 2, 3, 7, 11, 19, 43, 67, 163\}$. -/
@[category research solved, AMS 11]
theorem starkHeegner_classNumberOne :
    {k : ℕ | Squarefree k ∧ HasClassNumber k 1} = {1, 2, 3, 7, 11, 19, 43, 67, 163} := by
  sorry

/-- $163$ is squarefree. -/
@[category test, AMS 11]
theorem squarefree_163 : Squarefree (163 : ℕ) := by native_decide

/-- $\mathbb{Q}(\sqrt{-163})$ has class number $1$. -/
@[category API, AMS 11]
theorem hasClassNumber_163_1 : HasClassNumber 163 1 := by
  have h := starkHeegner_classNumberOne
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  exact ((h 163).mpr (by right; right; right; right; right; right; right; right; rfl)).2

/-- $163$ is the largest squarefree $k$ with class number $1$. -/
@[category test, AMS 11]
theorem a_1_163 : a 1 163 := by
  refine ⟨squarefree_163, hasClassNumber_163_1, ?_⟩
  intro m hm_sq hm_class
  have h := starkHeegner_classNumberOne
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have hm_in : m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Set ℕ) := (h m).mp ⟨hm_sq, hm_class⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm_in
  rcases hm_in with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- $427$ is the largest squarefree $k$ with class number $2$. -/
@[category test, AMS 11]
theorem a_2_427 : a 2 427 := by
  sorry

/-- $907$ is the largest squarefree $k$ with class number $3$. -/
@[category test, AMS 11]
theorem a_3_907 : a 3 907 := by
  sorry

/-- $1555$ is the largest squarefree $k$ with class number $4$. -/
@[category test, AMS 11]
theorem a_4_1555 : a 4 1555 := by
  sorry

/-- $163 \equiv 19 \pmod{24}$. -/
@[category test, AMS 11]
theorem mod_24_163 : 163 % 24 = 19 := by native_decide

/-- $427 \equiv 19 \pmod{24}$. -/
@[category test, AMS 11]
theorem mod_24_427 : 427 % 24 = 19 := by native_decide

/-- $907 \equiv 19 \pmod{24}$. -/
@[category test, AMS 11]
theorem mod_24_907 : 907 % 24 = 19 := by native_decide

/-- $1555 \equiv 19 \pmod{24}$. -/
@[category test, AMS 11]
theorem mod_24_1555 : 1555 % 24 = 19 := by native_decide

/-- All terms of A038552 are congruent to $19 \pmod{24}$. -/
@[category research open, AMS 11]
theorem mod_24_of_a (n k : ℕ) (h : a n k) : k % 24 = 19 := by
  sorry

/-- A038552 also gives the largest absolute value of negative fundamental discriminant
for each class number. -/
@[category research open, AMS 11]
theorem a_eq_largestNegFundDisc (n k : ℕ) (h : a n k) : IsLargestNegFundDiscForClassNumber n k := by
  sorry

/-- For even class number $n$, if $k$ is the largest odd squarefree number with
$h(-k) = n$ and $k'$ is the largest even squarefree number with $h(-k') = n$,
then $k > k'$. -/
@[category research open, AMS 11]
theorem odd_gt_even_for_even_classNumber (n : ℕ) (hn : Even n) (k k' : ℕ)
    (hk_odd : Odd k) (hk'_even : Even k')
    (hk_sq : Squarefree k) (hk'_sq : Squarefree k')
    (hk_class : HasClassNumber k n) (hk'_class : HasClassNumber k' n)
    (hk_largest : ∀ m, Odd m → Squarefree m → HasClassNumber m n → m ≤ k)
    (hk'_largest : ∀ m, Even m → Squarefree m → HasClassNumber m n → m ≤ k') :
    k > k' := by
  sorry

end OeisA038552
